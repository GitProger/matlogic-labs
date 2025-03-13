COMP=ocamlc

all: lex yacc cmi
	$(COMP) utils.ml parser.mli parser.ml lexer.ml base.ml helpers.ml main.ml -o main

run:
	./main

lex:
	ocamllex lexer.mll 

cmi:
	$(COMP) -c utils.ml

yacc:
	ocamlyacc parser.mly

clean:
	rm main
	rm *.cmi *.cmo parser.mli parser.ml lexer.ml

zip:
	zip -r `pwd`.zip . -x ".*" -x "_*" -x "main" \
	                   -x "*.o" -x "*.hi" \
	                   -x lexer.ml -x parser.ml
