extern "C" {
	auto malloc(size_t) -> void *;
}

struct List {
	List *list;
	unsigned long long element;
};

template <typename... Us>
auto make_list() -> List * {
	return (List *)1;
}

template <typename... Ts>
auto make_list(unsigned long long item, Ts... args) -> List * {
	auto const ptr = (List *) malloc(sizeof(List));
	*ptr = List {
		.list = make_list(args...),
		.element = item,
	};
	return ptr;
}
