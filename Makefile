build:
	dune build --release

install: build
	dune install

clean:
	dune clean
