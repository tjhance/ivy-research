

all:
	ocamlbuild -use-menhir -tag thread -use-ocamlfind main.native

parser:
	mkdir -p _build
	menhir --dump --explain ./Parser.mly --base _build/Parser

clean:
	rm -r _build