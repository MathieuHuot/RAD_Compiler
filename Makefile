all: build test

build:
	dune build --release @install

test: build
	dune runtest --release --no-buffer --force

test-full:
	dune exec -- ./test/test.exe -e

clean:
	dune clean

doc:
	dune build @doc-private

viewdoc: doc
	xdg-open _build/default/_doc/_html/syntax@4c5eccf64a65/Syntax/index.html

run:
	dune exec -- ./bin/main.exe

debugrun:
	OCAMLRUNPARAM=b dune exec -- ./bin/main.exe

.PHONY: all build test test-full clean doc viewdoc run debugrun
