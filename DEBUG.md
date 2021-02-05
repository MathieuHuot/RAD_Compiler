To run a test with a seed
```bash
QCHECK_SEED=916673111 make test
```

To open utop in the project
```bash
make utop
```

To parse a term
```ocaml
let expr = CCResult.get_or_failwith (Source.Parse.of_string "(x1:real * x1:real)");;
```
