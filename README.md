# Dependently-Typed Data Plane Programming with Π4

This repository contains the implementation of Π4, a dependently-typed variant of the P4 language based on regular types with decidable refinements that is capable of expressing and modularly reasoning about a rich set of network properties.

The full paper is available at https://doi.org/10.1145/3498701.

## Building

1. Install OPAM following the official installation instructions

1. Pin and install external dependencies *petr4* and *ocaml-z3*
    ```
    opam pin add petr4 https://github.com/verified-network-toolchain/petr4
    opam pin add z3 https://github.com/eichholz/ocaml-z3.git#use-successes
    ```

1. Use OPAM to install dependencies: 
    ```
    opam install --deps-only
    ```

## Running

### Tests

Run the following command from the project's root directory, to run all tests. 
The optional argument `--no-buffer` disables dune's buffering mechanism. 
```
dune runtest --no-buffer
```

To pass addititional arguments to the test runner, run:
```
dune exec test/test.exe test [ARGS]
```

For example, to execute only the typechecking tests, run:
```
dune exec test/test.exe test type_checking
```

### Profiling

https://github.com/LexiFi/landmarks

```
dune exec --context profiling -- bin/main.exe -- [ARGS]
dune exec --context profiling -- test/test.exe -- [ARGS]
```
