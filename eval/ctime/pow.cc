auto add(unsigned long long x, unsigned long long y) -> unsigned long long {
	unsigned long long z = y;
	for (size_t i{0}; i < x; ++i) {
		z = z + 1;
	}
	return z;
}

auto mul(unsigned long long x, unsigned long long y) -> unsigned long long {
	unsigned long long z = 0;
	for (size_t i{0}; i < x; ++i) {
		z = add(y, z);
	}
	return z;
}

auto pow(unsigned long long x, unsigned long long y) -> unsigned long long {
	unsigned long long z = 1;
	for (size_t i{0}; i < x; ++i) {
		z = mul(y, z);
	}
	return z;
}
