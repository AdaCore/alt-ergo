all: split test

split: split.ml
	ocamlopt split.ml -o split
  
split.ml: split.mll
	ocamllex split.mll

test: test.ml
	ocamlopt test.ml -o test
  
test.ml: test.mll
	ocamllex test.mll

clean: 
	rm -f split.ml split.cm* split.o split test.ml test.cm* test.o test