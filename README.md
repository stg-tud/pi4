# Pi4

Typechecker for a dependently-typed variant of P4.

## Building

### External Dependencies
https://github.com/eichholz/ocaml-z3

### Build documentation
```dune build @doc```

The documentation is available in `_build/default/_doc/`.

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
export OCAML_LANDMARKS="format=json,output=./profile.json,debug"
```

The viewer for the generated output can be found here: http://lexifi.github.io/landmarks/viewer.html
