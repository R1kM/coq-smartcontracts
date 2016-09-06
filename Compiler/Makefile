CMO=  lexer.cmo parser.cmo passes.cmo lemmas.cmo codegen.cmo main.cmo 
GENERATED=lexer.ml tokens.ml tokens.mli parser.mli parser.ml

CFLAGS=-annot -g
COMPILER=ocamlc $(CFLAGS)

LFLAGS=
LEXER=ocamllex $(LFLAGS)

PFLAGS=-v --dump --explain --graph
PARSER=menhir $(PFLAGS)


solidity-coq: $(PDF) $(CMO)
	$(COMPILER) -o $@ $(CMO)


.SUFFIXES: .mli .ml .cmi .cmo .mll .mly
.mli.cmi:
	$(COMPILER) -c  $<

.ml.cmo:
	$(COMPILER) -c $<

.mll.ml:
	$(LEXER) $<

tokens.ml tokens.mli: tokens.mly
	$(PARSER) --only-tokens tokens.mly

parser.ml parser.mli: parser.mly
	$(PARSER) --base parser --external-tokens Tokens -v tokens.mly parser.mly 

.PHONY: clean
clean:
	-rm $(GENERATED)
	-rm -f *.cm[io] *.o *.annot *~ *.tgz *.tar *.swp
	-rm -f *.automaton *.conflicts *.dot # menhir generated files
	-rm .depend

.depend depend:$(GENERATED)
	-rm -f .depend
	-ocamldep *.ml *.mli > .depend

include .depend
