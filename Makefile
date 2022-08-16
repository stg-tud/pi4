all: build

clean:
	dune clean

build: 
	dune build; rm -f ./pi4; cp _build/default/bin/main.exe ./pi4


ARTIFACT-DIR = ./artifact-examples
artifact: $(ARTIFACT-DIR)/*.pi4
	for f in $(sort $^); do echo; echo $${f} using type $${f}_type; ./pi4 -m 320 -ir $${f} -typ $${f}_type; done

run:
	dune exec bin/main.exe

.PHONY: test
test: 
	OCAMLRUNPARAM="b" dune exec -- test/test.bc test -q
