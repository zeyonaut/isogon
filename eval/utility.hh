#pragma once

#include <cstdint>

using u8 = uint8_t;
using u16 = uint16_t;
using u64 = uint64_t;
using usize = size_t;

#include <optional>
#include <string_view>

template <typename T>
auto parse(const std::string_view string) -> T {
	int result;
	if (std::from_chars(string.data(), string.data() + string.size(), result)
			 .ec
		== std::errc {}) {
		return result;
	} else {
		abort();
	}
}

#include <numeric>

auto sample_mean(std::vector<double> const &samples) -> double {
	return std::accumulate(samples.begin(), samples.end(), 0.0) / samples.size();
}

auto sample_std(std::vector<double> const &samples) -> double {
	double mean = sample_mean(samples);
	double sum = std::accumulate(samples.begin(), samples.end(), 0.0, [mean](double const &x, double const &y) { return x + ((y - mean) * (y - mean)); });
	return std::sqrt(sum / (samples.size() - 1));
}

struct BenchResult {
	double mean;
	double std;
};
