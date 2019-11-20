# AlgoWMutable

## Benchmark

On XPS-13 (XPS 13 9350), with GHC 8.6.4:

```
Preprocessing library for AlgoWMutable-0.1.0.0..
Building library for AlgoWMutable-0.1.0.0..
Preprocessing benchmark 'bench' for AlgoWMutable-0.1.0.0..
Building benchmark 'bench' for AlgoWMutable-0.1.0.0..
Running 1 benchmarks...
Benchmark bench: RUNNING...
benchmarking factorial
time                 16.34 μs   (16.23 μs .. 16.44 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 16.35 μs   (16.25 μs .. 16.49 μs)
std dev              410.8 ns   (311.2 ns .. 549.2 ns)
variance introduced by outliers: 26% (moderately inflated)

benchmarking factorialNoRecords
time                 10.91 μs   (10.86 μs .. 10.97 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 10.88 μs   (10.83 μs .. 10.97 μs)
std dev              248.0 ns   (169.5 ns .. 389.5 ns)
variance introduced by outliers: 24% (moderately inflated)

benchmarking solveDepressedQuartic
time                 148.1 μs   (147.3 μs .. 148.9 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 146.2 μs   (145.6 μs .. 147.0 μs)
std dev              2.269 μs   (1.937 μs .. 2.855 μs)
```
