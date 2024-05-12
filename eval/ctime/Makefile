temporary=tmp

setup:
	cargo build --manifest-path ../../Cargo.toml --release

unzip:
	rm -rf $(temporary)
	mkdir "$(temporary)"
	pbench --stdout-nul clang -std=c++20 unzip.cc -c -o $(temporary)/unzip.cc.o 
	pbench --stdout-nul ../../target/release/isogon -f unzip.is -o $(temporary)/unzip.is.o

fib:
	rm -rf $(temporary)
	mkdir "$(temporary)"
	pbench --stdout-nul clang -std=c++20 fib.cc -c -o $(temporary)/fib.cc.o 
	pbench --stdout-nul ../../target/release/isogon -f fib.is -o $(temporary)/fib.is.o
	
pow:
	rm -rf $(temporary)
	mkdir "$(temporary)"
	pbench --stdout-nul clang -std=c++20 pow.cc -c -o $(temporary)/pow.cc.o 
	pbench --stdout-nul ../../target/release/isogon -f pow.is -o $(temporary)/pow.is.o

mklist:
	rm -rf $(temporary)
	mkdir "$(temporary)"
	pbench --stdout-nul clang -std=c++20 mklist.cc -c -o $(temporary)/mklist.cc.o 
	pbench --stdout-nul ../../target/release/isogon -f mklist.is -o $(temporary)/mklist.is.o

.PHONY: unzip fib pow mklist
