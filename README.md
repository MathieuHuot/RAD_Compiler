### Installation

To build the project
```bash
make build
```
To run the project
```bash
dune exec -- ./bin/main.exe
```
Currently print some test in out.txt

To run tests
```bash
make
```

To run tests and print counter example for all failing test or to run multiple time test.
```bash
make test-full
```

To build the doc
```bash
make doc
```
Main page of the module Syntax is `_build/default/_doc/_html/syntax@4c5eccf64a65/Syntax/index.html`

To view the doc
```bash
make viewdoc
```

### Content

This project provides efficient purely functional forward-mode and reverse mode automatic differentiation.
Currently, the input and output are an AST in OCaml.

### Detail of the source code

- `syntax` contains the source and target AST, and some all the basic operations on them
- `transforms` contains the `ANF`, `ForwardMode`, `ReverseMode`, and different `Jets` source-code transformations
- `rewrite` contains optimisations and optimisation strategies.
