#include <cassert>
#include <charconv>
#include <chrono>
#include <cstdio>
#include <iostream>
#include <memory>
#include <span>
#include <vector>

#include "../utility.hh"

extern "C" {
	auto entry(u64) -> u64;
}

auto fib_c(u64 n) -> u64 {
	u64 left {0};
	u64 right {1};
	for (size_t i {0}; i < n; ++i) {
		u64 tmp = left;
		left = right;
		right += tmp;
	}
	return left;
}

auto bench(u64 sample_count, u64 range, u64 repetitions, auto(*fn)(u64)->u64) -> std::vector<BenchResult> {
	std::vector<BenchResult> results {};
	for (u64 n {0}; n < range; ++n) {
		std::vector<double> sample_results {};
		for (size_t i {0}; i < sample_count; ++i) {
			auto start = std::chrono::steady_clock::now();
			for (size_t r {0}; r < repetitions; ++r) fn(n);
			auto end = std::chrono::steady_clock::now();
			auto duration = std::chrono::duration<double>(end - start).count();
			auto result = duration; // / (size * size);
			sample_results.push_back(result);
		}
		results.push_back(BenchResult {
			.mean = sample_mean(sample_results),
			.std = sample_std(sample_results)});
	}
	return results;
}

auto run(std::span<std::string_view> args) {
	// Parse arguments.
	assert(args.size() == 1);
	auto sample_count = parse<u64>(args[0]);

	auto range = 16;
	auto isogon_results = bench(sample_count, range, 100000, entry);
	auto cxx_results = bench(sample_count, range, 100000, fib_c);
	std::cout << "index, isogon_mean, isogon_std, cxx_mean, cxx_std" << '\n';

	for (u64 i {0}; i < range; ++i) {
		std::cout
			<< std::setprecision (17)
			<< i
			<< ", "
			<< isogon_results[i].mean
			<< ", "
			<< isogon_results[i].std
			<< ", "
			<< cxx_results[i].mean
			<< ", "
			<< cxx_results[i].std
			<< "\n";
	}
}

auto main(int argc, char **argv) -> int {
	static std::vector<std::string_view> args(argv + 1, argv + argc);
	run(args);
}
