#include <array>
#include <bit>
#include <cassert>
#include <charconv>
#include <chrono>
#include <cstdio>
#include <iomanip>
#include <iostream>
#include <memory>
#include <span>
#include <vector>

#include "../utility.hh"

template <typename T>
struct List {
	List<T> *list;
	T element;
};

template <typename T>
struct SizedList {
	u64 len;
	List<T> *list;
};

struct Pair {
	u64 x;
	u64 y;
};

struct Output {
	List<u64> *a;
	List<u64> *b;
};

extern "C" {
	// Isogon implementation.
	auto entry(SizedList<Pair> *, Output *) -> void;
}

// C++ implementation.
auto helper(u64 len, List<Pair> *list, Output *output) -> void {
	if (len == 0) {
		output->a = std::bit_cast<List<u64> *>(u64 {1});
		output->b = std::bit_cast<List<u64> *>(u64 {1});
	} else {
		helper(len - 1, list->list, output);
		auto a_prev = output->a;
		output->a = static_cast<List<u64> *>(malloc(sizeof(List<Pair>)));
		output->a->list = a_prev;
		output->a->element = list->element.x;
		auto b_prev = output->b;
		output->b = static_cast<List<u64> *>(malloc(sizeof(List<Pair>)));
		output->b->list = b_prev;
		output->b->element = list->element.y;
		free(list);
	}
}

auto free_num_list(u64 len, List<u64> *list) -> void {
	if (len > 0) {
		free_num_list(len - 1, list->list);
		free(list);
	}
}

auto unzip_c(SizedList<Pair> *sized_list, Output *output) -> void {
	helper(sized_list->len, sized_list->list, output);
}

auto make_list_of_pairs(u64 n) -> SizedList<Pair> {
	List<Pair> *list = nullptr;
	for (u64 i {0}; i < n; ++i) {
		auto ptr = (List<Pair> *)malloc(sizeof(List<Pair>));
		*ptr = List<Pair> {.list = list,
			.element = Pair {
				.x = i,
				.y = 2 * i,
			}};
		list = ptr;
	}
	return SizedList<Pair> {.len = n, .list = list};
}

auto make_list(u64 n) -> SizedList<u64> {
	List<u64> *list = nullptr;
	for (u64 i {0}; i < n; ++i) {
		auto ptr = (List<u64> *)malloc(sizeof(List<u64>));
		*ptr = List<u64> {
			.list = list,
			.element = i,
		};
		list = ptr;
	}
	return SizedList<u64> {.len = n, .list = list};
}

auto print_list(u64 len, List<u64> *list) {
	for (u64 i {0}; i < len; ++i) {
		std::cout << list->element << ", ";
		list = list->list;
	}
	std::cout << "\n";
}

auto bench(u64 sample_count, std::span<u64> sizes, auto(*fn)(SizedList<Pair> *, Output *)->void) -> std::vector<BenchResult> {
	std::vector<BenchResult> results {};
	for (auto const size : sizes) {
		std::vector<double> sample_results {};
		for (size_t i {0}; i < sample_count; ++i) {
			auto sized_list = make_list_of_pairs(size);
			Output output {};
			auto start = std::chrono::steady_clock::now();
			fn(&sized_list, &output);
			auto end = std::chrono::steady_clock::now();
			free_num_list(size, output.a);
			free_num_list(size, output.b);
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

	std::array<u64, 10> sizes {500, 1000, 1500, 2000, 2500, 3000, 3500, 4000, 4500, 5000};

	auto isogon_results = bench(sample_count, sizes, entry);
	auto cxx_results = bench(sample_count, sizes, unzip_c);
	std::cout << "size, isogon_mean, isogon_std, cxx_mean, cxx_std" << '\n';

	for (u64 i {0}; i < sizes.size(); ++i) {
		std::cout
			<< std::setprecision (17)
			<< sizes[i]
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
