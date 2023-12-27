all: alex happy
	ghc lexer parser utils main -o ord

run:
	./ord

alex:
	alex lexer.x

happy:
	happy parser.y

clean:
	rm lexer.hs parser.hs *.hi *.o
