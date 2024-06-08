# use veridater for ci testing

.PHONY: test_all gen_test clean

SRC:=

test_all: 
	make -C tests all

gen_test:
	make -C tests gen_test

clean:
	rm -rf build/*


