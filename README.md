<div align="center">
<br>

# Isogon

A dependently-typed programming language for performance-critical software.

<br>
</div>

## What is Isogon?

Isogon is an experimental programming language supporting dependent types, stack-allocated data, and memory safety without garbage collection.
To achieve this, Isogon borrows ideas from [two-level type theory](https://andraskovacs.github.io/pdfs/2ltt.pdf) and [quantitative type theory](https://bentnib.org/quantitative-type-theory.pdf) to enable static polymorphism over memory representations (as an application of its dependently-typed metaprogramming facilities) and enforced move semantics.

## Repository overview

This repository contains a compiler for Isogon, which is segmented into two pipelines:

- The [frontend](src/frontend/) type-checks and elaborates Isogon's surface syntax, automatically verifying that programs adhere to its ownership discipline.

- The [backend](src/backend/) provides code generation for Isogon, powered by the [Cranelift](https://cranelift.dev/) intermediate representation.

A test suite is provided in [/tests/](/tests/), alongside a broad selection of [example programs](/examples/) which showcase the features implemented in Isogon.

## License

Isogon is distributed under the terms of the MIT license.

See [LICENSES/MIT.txt](LICENSES/MIT.txt) for details.

## Getting started

To get started with Isogon, run the `help` command with:
```
cargo run -- -h
```
The following command compiles an example program to an object file:
```
cargo run -- -f examples/fib_input.is -o out/fib_input.o
```
