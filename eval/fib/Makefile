temporary=tmp

all:
	rm -rf $(temporary)
	mkdir "$(temporary)"
	cargo run --manifest-path ../../Cargo.toml -- -f fib.is -o $(temporary)/fib.o
	clang -std=c++20 main.cc $(temporary)/fib.o -o $(temporary)/eval.exe
	
c:
	clang -std=c++20 main.cc $(temporary)/fib.o -o $(temporary)/eval.exe

clif:
	cargo run --manifest-path ../../Cargo.toml -- -f fib.is --clif

.PHONY: all clean
