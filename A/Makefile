all: alex happy
	ghc lexer parser utils main -o main

run:
	./main

alex:
	alex lexer.x

happy:
	happy parser.y

clean:
	rm lexer.hs parser.hs *.hi *.o

zip:
	zip -r `pwd`.zip . -x ".*" -x "_*" -x "main" \
	                   -x "*.o" -x "*.hi" \
	                   -x lexer.hs -x parser.hs