### Installation

To build the project
```bash
dune build @install
```

To run tests and compare them with test.expected
```bash
dune runtest
```

To run tests and print them in test.expected
```bash
dune runtest --auto-promote
```

To run the project
```bash
dune exec -- ./bin/main.exe
```
Currently print some test in out.txt

To run tests and print the results with small example when failing
```bash
dune exec -- ./test/test.exe -e
```

### Content

This project provides efficient purely functionnal forward-mode and reverse mode automatic differentiation.
Currently, the input and output are an AST in OCaml.

### Detail of the source code

- `syntax` contains the source and target AST, and some all the basic operations on them
- `transforms` contains the `ANF`, `ForwardMode`, `ReverseMode`, and different `Jets` source-code transformations
- `rewrite` contains optimisations and optimisation strategies.