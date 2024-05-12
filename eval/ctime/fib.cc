auto fib_c(unsigned long long n) -> unsigned long long {
	unsigned long long left {0};
	unsigned long long right {1};
	for (size_t i {0}; i < n; ++i) {
		auto const tmp = left;
		left = right;
		right += tmp;
	}
	return left;
}
