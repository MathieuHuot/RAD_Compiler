### Installation

To build the project
```ocaml
dune build @install
```

To run tests and compare them with test.expected
```ocaml
dune build @runtest
```

To run tests and print them in test.expected
```ocaml
dune build @runtest --auto-promote
```

To run the project
```ocaml
dune exec ./bin.exe 
```

### Content

This project provides efficient purely functionnal forward-mode and reverse mode automatic differentiation.
Currently, the input and output are an AST in OCaml.

### Detail of the source code

- `syntax` contains the source and target AST, and some all the basic operations on them
- `transforms` contains the `ANF`, `ForwardMode` and `ReverseoMode` source-code transformations
- `rewrite` contains optimisations and optimisation strategies.