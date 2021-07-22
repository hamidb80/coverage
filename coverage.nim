import macros, tables, strutils, os, sequtils

type 
    CovData* = tuple[lineNo: int, passes: int]
    CovChunk* = seq[CovData]
    CovChunkInfo* = tuple[
        fileName,
        procName: string, 
        lineRange: HSlice[int, int]]

    CovReport* = tuple[procInfo: CovChunkInfo, coveredLines, uncoveredLines:seq[int], tracked: int]


var procBounderies: Table[ptr CovChunk, CovChunkInfo]

proc getFileName(n: NimNode): string =
    let ln = n.lineInfo
    let i = ln.rfind('(')
    result = ln.substr(0, i - 1)

proc getLineNumber(n: NimNode): int =
    let ln = n.lineInfo
    let i = ln.rfind('(')
    let j = ln.rfind(',')
    result = parseInt(ln.substr(i + 1, j - 1))

proc getLastLineNumber(node: NimNOde, firstLine: int = 0): int=
  if node.len > 0:
    getLastLineNumber(node[^1], node.lineInfoObj.line)
  else:
    firstline

proc registerCovChunk(fileName, procName: string, lineRange: HSlice[int, int], chunk: var CovChunk) =
    procBounderies[addr chunk] = (fileName, procName, lineRange)

proc transform(n, track, list: NimNode, forceAdd=false): NimNode {.compileTime.} =
    result = copyNimNode(n)
    for c in n.children:
        result.add c.transform(track, list)

    if forceAdd or n.kind in {nnkElifBranch, nnkOfBranch, nnkExceptBranch, nnkElse}:
        template trackStmt(track, i) =
            {.cast(gcsafe).}: # for funcDefs
                inc track[i].passes
        template tup(lineno) = 
            (lineno, 0)

        let lineno = result[^1].getlineNumber
        result[^1] = newStmtList(getAst trackStmt(track, list.len), result[^1])
        list.add(getAst tup(lineno))

macro cov*(body: untyped): untyped =
    when defined(release) and not defined(enableCodeCoverage):
        result = body
    else:
        let filename = body.getFileName
        var trackSym = genSym(nskVar, "track")
        var trackList = newNimNode(nnkBracket)

        let 
            startLine = body.lineInfoObj.line
            endLine = body.getLastLineNumber

        var listVar = newStmtList(
            newNimNode(nnkVarSection).add(
                newNimNode(nnkIdentDefs).add(
                    trackSym, 
                    newNimNode(nnkBracketExpr).add(
                        newIdentNode("seq"), 
                        newIdentNode("CovData")
                    ), 
                    prefix(trackList, "@"))),
                newCall(
                    bindSym "registerCovChunk", 
                    newStrLitNode(filename), 
                    newStrLitNode body.name.strVal,
                    newNimNode(nnkInfix).add(
                        ident"..",
                        startLine.newIntLitNode,
                        endLine.newIntLitNode,
                    ),
                    trackSym
            ))

        result = newStmtList(listVar, transform(body,trackSym, trackList, true))
        debugecho result.repr

# report -------------------------------------------------

proc coverageReport*(): seq[CovReport] =
    for covChunkRef, info in procBounderies:
        var report: CovReport
        let covChunk = covChunkRef[]
        report.tracked = covChunk.len
        report.procInfo = info

        for line in covChunk:
            if line.passes == 0: 
                report.uncoveredLines.add line.lineNo
            else:
                report.coveredLines.add line.lineNo

        result.add report

proc coveredLinesInFile*(reports: seq[CovReport], fileName: string): seq[int] =
    for r in reports:
        if r.procInfo.fileName == fileName:
            result.add r.coveredLines

proc coverageInfoByFile*(reports: seq[CovReport]): Table[string, tuple[covered,tracked: int]] =
    template addToRes(fname:string,cvrd, trckd: int)=
        if fname in result:
            result[fname].covered += cvrd
            result[fname].tracked += trckd
        else:
            result[fname] = (cvrd, trckd)

    for r in reports:
        for r in reports:
            r.procInfo.fileName.addToRes(r.coveredLines.len, r.tracked)

proc coveragePercentageByFile*(): Table[string, float] =
    for fname, info in coverageInfoByFile(coverageReport()):
        result[fname] = info.covered.float / info.tracked.float

proc incompletelyCoveredProcs*(reports: seq[CovReport]): seq[CovReport]=
    reports.filterIt it.uncoveredLines.len != 0

proc totalCoverage*(reports: seq[CovReport]): float =
    var total, covered: int
    for r in reports:
        total.inc r.tracked
        covered.inc r.coveredLines.len

    covered / total

#[
when not defined(js) and not defined(emscripten):
    import os, osproc
    import json
    import httpclient
    import md5

    proc initCoverageDir*(path: string = ".") =
        putEnv("NIM_COVERAGE_DIR", path)

    proc saveCovResults() {.noconv.} =
        let jCov = newJObject()
        for k, v in coverageResults:
            let jChunks = newJArray()
            for chunk in v:
                let jChunk = newJArray()
                for ln in chunk[]:
                    let jLn = newJArray()
                    jLn.add(newJInt(ln.lineNo))
                    jLn.add(newJInt(ln.passes))
                    jChunk.add(jLn)
                jChunks.add(jChunk)
            jCov[k] = jChunks
        
        var i = 0
        while true:
            let covFile = getEnv("NIM_COVERAGE_DIR") / "cov" & $i & ".json"
            if not fileExists(covFile):
                writeFile(covFile, $jCov)
                break
            inc i

    proc expandCovSeqIfNeeded(s: var seq[int], toLen: int) =
        if s.len <= toLen:
            s.add (-1).repeat(tolen - s.len)

    proc createCoverageReport*() =
        let covDir = getEnv("NIM_COVERAGE_DIR")
        var i = 0
        var covData = initTable[string, seq[int]]()

        while true:
            let covFile = getEnv("NIM_COVERAGE_DIR") / "cov" & $i & ".json"
            if not fileExists(covFile):
                break
            inc i
            let jf = parseJson(readFile(covFile))
            for fileName, chunks in jf:
                if fileName notin covData:
                    covData[fileName] = @[]

                for chunk in chunks:
                    for ln in chunk:
                        let lineNo = int(ln[0].num)
                        let passes = int(ln[1].num)
                        expandCovSeqIfNeeded(covData[fileName], lineNo)
                        if covData[fileName][lineNo] == -1:
                            covData[fileName][lineNo] = 0
                        covData[fileName][lineNo] += passes
            
            removeFile(covFile)

        let jCovData = newJObject()
        for k, v in covData:
            jCovData[k] = %* {
                "l": v,
                "s": readFile(k) # get Source Code
            }

        const htmlTemplate = staticRead("coverageTemplate.html")
        writeFile(getEnv("NIM_COVERAGE_DIR") / "cov.html", htmlTemplate.replace("$COV_DATA", $jCovData))

    if getEnv("NIM_COVERAGE_DIR").len > 0:
        addQuitProc(saveCovResults)

    proc sendCoverageResultsToCoveralls*() =
        var request = newJObject()
        if existsEnv("TRAVIS_JOB_ID"):
            request["service_name"] = % "travis-ci"
            request["service_job_id"] = % getEnv("TRAVIS_JOB_ID")

            # Assume we're in git repo. Paths to sources should be relative to repo root
            let gitRes = execCmdEx("git rev-parse --show-toplevel")
            if gitRes.exitCode != 0:
                raise newException(Exception, "GIT Error")

            let curDir = getCurrentDir()

            # TODO: The following is too naive!
            let relativePath = curDir.substr(gitRes.output.len)

            var files = newJArray()
            for k, v in coverageResults:
                let lines = coveredLinesInFile(k)
                var jLines = newJArray()
                var curLine = 1
                for data in lines:
                    while data.lineNo > curLine:
                        jLines.add(newJNull())
                        inc curLine
                    jLines.add(newJInt(data.passes))
                    inc curLine
                
                files.add (%* {
                    "name": relativePath / k,
                    "coverage": jLines,
                    "source_digest": getMD5(readFile(k)),
                    #"source" = newJString(readFile(k))
                })

            request["source_files"] = files
            var data = newMultipartData()
            echo "COVERALLS REQUEST: ", $request
            data["json_file"] = ("file.json", "application/json", $request)
            echo "COVERALLS RESPONSE: ", newHttpClient().postContent("https://coveralls.io/api/v1/jobs", multipart=data)
]#