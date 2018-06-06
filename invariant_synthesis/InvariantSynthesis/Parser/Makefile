

all:
	ocamlbuild -use-menhir -tag thread -use-ocamlfind main.native

menhir:
	mkdir -p _build
	menhir --dump --explain ./ExprParser.mly --base _build/ExprParser

clean:
	rm -r _build