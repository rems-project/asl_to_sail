BUILD = ocamlbuild -cflag -g -lflag -g -use-ocamlfind

default:
	$(BUILD) main.native
	cp main.native asl_to_sail

byte:
	$(BUILD) main.byte

clean:
	ocamlbuild -clean
	rm -f asl_to_sail
