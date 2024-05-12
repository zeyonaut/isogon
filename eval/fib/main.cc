#include <memory>
#include <cstdio>
#include <cstdint>
#include <iostream>
#include <vector>
#include <span>
#include <string_view>
#include <optional>
#include <charconv>
#include <cassert>
#include <chrono>

using u8 = uint8_t;
using u16 = uint16_t;
using u64 = uint64_t;

extern "C" {
	auto entry(u64) -> u64;
}

template<typename T> auto parse(const std::string_view string) -> std::optional<T> {
	int result;
	if (std::from_chars(string.data(), string.data() + string.size(), result).ec == std::errc {}) {
		return result;
	} else {
		return {};
	}
}

auto fib(u64 n) -> u64 {
	u64 left{0};
	u64 right{1};
	for (size_t i{0}; i < n; ++i) {
		u64 tmp = left;
		left = right;
		right += tmp;
	}
	return left;	
}

auto run(std::span<std::string_view> args) {
	// Parse arguments.
	assert(args.size() == 2);
	auto x = parse<u64>(args[0]);
	auto top = parse<u64>(args[1]);
	if (!x) {
		return;
	}

	auto num_iterations = *x;

	auto start = std::chrono::steady_clock::now();
	for (size_t i{0}; i < num_iterations; ++i) {
		for (size_t n{0}; n < *top; ++n) {
			entry(n);
		}
	}
	auto end = std::chrono::steady_clock::now();

	std::cout << "Isogon: " << end - start << '\n';

	auto start_2 = std::chrono::steady_clock::now();
	for (size_t i{0}; i < num_iterations; ++i) {
		for (size_t n{0}; n < *top; ++n) {
			fib(n);
		}
	}
	auto end_2 = std::chrono::steady_clock::now();

	std::cout << "C++: " << end_2 - start_2 << '\n';
}


auto main(int argc, char **argv) -> int {
	static std::vector<std::string_view> args(argv + 1, argv + argc);
	run(args);
}

