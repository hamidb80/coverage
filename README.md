# coverage
Code coverage library for Nim. Inspired by [Andreas Rumpf talk at OSCON](https://github.com/Araq/oscon2015).

## Usage
```nim
import coverage

proc myProcToCover(x: int) {.cov.} = # Add cov pragma to proc definition to enable code coverage.
  if x == 0:
    echo "x is 0"
  else:
    echo "x is ", x

# Run your program or unittest
myProcToCover(1)

# At the end of the program, display coverage results:
echo "BY FILE: ", coveragePercentageByFile()
# Outputs: BY FILE: {test.nim: 0.5}

echo "TOTAL: ", totalCoverage()
# Outputs: TOTAL: 0.5

# Finer grained information may accessed with coverageInfoByFile proc.
```

### Notes
- Code coverage is disabled if ```release``` is defined. Define ```enableCodeCoverage``` option to keep it enabled in release mode.
