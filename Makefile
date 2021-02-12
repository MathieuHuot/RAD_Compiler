RELEASE=--release

all: build test

build:
	dune build $(RELEASE) @install

test: build
	dune runtest $(RELEASE) --no-buffer --force

test-full:
	dune exec $(RELEASE) -- ./test/test.exe -e

clean:
	dune clean

doc:
	dune build $(RELEASE) @doc-private

viewdoc: doc
	xdg-open _build/default/_doc/_html/syntax@4c5eccf64a65/Syntax/index.html

run:
	dune exec $(RELEASE) -- ./bin/main.exe

debugrun:
	OCAMLRUNPARAM=b dune exec $(RELEASE) -- ./bin/main.exe

utop:
	OCAMLRUNPARAM=b dune utop $(RELEASE)

.PHONY: all build test test-full clean doc viewdoc run debugrun utop
