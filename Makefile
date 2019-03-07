OCB_FLAGS = -I src -I lib
OCB = ocamlbuild $(OCB_FLAGS)

test: main.native mini-c
	./mini-c --debug test.c

main.native: ./src/*.ml*
	$(OCB) $@

mini-c:
	ln -s main.native $@

clean:
	$(OCB) -clean
	rm mini-c
