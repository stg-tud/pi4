# Pi4

Typechecker for a dependently-typed variant of P4 including optimizations for heap type inlining and caching.

## Building

### External Dependencies
- https://github.com/eichholz/ocaml-z3
- Z3 >= [4.8.17](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.17)

### Building from source (Linux & macOS)

This setup was tested on Ubuntu 22.04 and macOS Monterey

1. Install OCaml (Tested with 4.11.1), opam (Tested with 2.1.2), and Z3(Tested with 4.8.17)

2. Clone the repository and switch to the `mt-inlining` branch:

   ```
   git clone https://github.com/stg-tud/pi4.git
   cd pi4
   git checkout mt-inlining
   ```

3. Create a new environment using OCaml compiler version 4.11.1 and load the new environment:

   ```
   opam switch create pi4 ocaml-base-compiler.4.11.1
   eval $(opam env --switch=pi4)
   ```

4. Install dune version 2.9.1:

   ```
   opam install dune.2.9.1
   ```

5. Use opam to install menhir:

   ```
   opam install menhir
   ```

6. Pin version 0.1.2 of Petr4:

   ```
   opam pin https://github.com/verified-network-toolchain/petr4.git#0.1.2
   ```

7. Pin the custom z3 library:

   ```
   opam pin https://github.com/eichholz/ocaml-z3.git#use-successes
   ```

8. Install additional dependencies:

   ```
   opam install core fmt landmarks landmarks-ppx logs owl-base alcotest ANSITerminal
   ```

9. Build the project:

   ```
   dune build
   ```



## Tests

Tests can be executed by using dune. The general test set for substitution inlining may be executed using the following command:

```
dune exec test/test.exe test substitution_base
```

## Benchmarking

The `./benchmark` directory contains multiple files used for benchmarking.

- The `programs` directory contains all Pi4 programs and types used for benchmarking.
- `benchmark.ml` contains the benchmarking CLI written in OCaml.
- `benchmark.py` contains the actual benchmark script using the CLI.
- `benchmark.ipynb` contains the code used to create benchmarking graphs.
- `cache_metrics.py` contains a script for collecting cache hit and miss data.
- `cache_metrics.ipynb` contains the visualization of cache hit rates.
- `cache.csv` contains the cache hit rates used in the thesis.
- `profile_tut_basic.csv` contains the profiling data used in the thesis.
- `profiles.ipynb` contains the visualization of profiling data.
- `results_final.csv` contains the benchmarking results used in the thesis.

### Running the Benchmark

The benchmark can be run by executing the following command within the `./benchmark` directory:

```
python3 benchmark.py
```

The results are written to `results.csv` and can be visualized using the `benchmark.ipynb` notebook by changing the `input_file` variable to `results.csv`.

### Running the Cache Profiler

The cache metrics can be reproduced using the following command:

```
python3 cache_metrics.py
```

### Profiling the Typechecking Process

The profiling of the typechecking of individual commands must be done manually and executed from the project's root directory. For instance, the `tut_basic_safe` program can be profiled by executing the :

```
dune exec --context profiling -- benchmark/benchmark.exe benchmark/programs/tut_basic_safe.pi4 -t benchmark/programs/tut_basic_safe.pi4_type
```

The individual optimizations can be enabled by adding `-f` for substitution inlining, `-i` for instance caching and `-n` for length caching.



