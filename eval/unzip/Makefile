name=unzip
temporary=tmp

all:
	rm -rf $(temporary)
	mkdir "$(temporary)"
	cargo run --manifest-path ../../Cargo.toml -- -f $(name).is -o $(temporary)/$(name).o
	clang -std=c++20 main.cc $(temporary)/$(name).o -o $(temporary)/eval.exe
	$(temporary)/eval 1000

c: 
	clang -std=c++20 main.cc $(temporary)/$(name).o -o $(temporary)/eval.exe

clif:
	cargo run --manifest-path ../../Cargo.toml -- -f $(name).is --clif

data:
	$(temporary)/eval 1000

.PHONY: all clean
