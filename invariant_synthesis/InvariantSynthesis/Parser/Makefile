

all:
	ocamlbuild -use-menhir -tag thread -use-ocamlfind main.native

expr:
	mkdir -p _build
	menhir --dump --explain ./ExprParser.mly --base _build/ExprParser

stat:
	mkdir -p _build
	menhir --dump --explain ./StatParser.mly --base _build/StatParser

clean:
	rm -r _build