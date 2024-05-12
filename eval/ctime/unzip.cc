template <typename T>
struct List {
	List<T> *list;
	T element;
};

template <typename T>
struct SizedList {
	unsigned long long len;
	List<T> *list;
};

struct Pair {
	unsigned long long x;
	unsigned long long y;
};

struct Output {
	List<unsigned long long> *a;
	List<unsigned long long> *b;
};

extern "C" {
	auto malloc(size_t) -> void *;
	auto free(void *) -> void;
}

// C++ implementation.
auto helper(unsigned long long len, List<Pair> *list, Output *output) -> void {
	if (len == 0) {
		output->a = (List<unsigned long long> *)(1);
		output->b = (List<unsigned long long> *)(1);
	} else {
		helper(len - 1, list->list, output);
		auto a_prev = output->a;
		output->a = static_cast<List<unsigned long long> *>(malloc(sizeof(List<Pair>)));
		output->a->list = a_prev;
		output->a->element = list->element.x;
		auto b_prev = output->b;
		output->b = static_cast<List<unsigned long long> *>(malloc(sizeof(List<Pair>)));
		output->b->list = b_prev;
		output->b->element = list->element.y;
		free(list);
	}
}

auto unzip_c(SizedList<Pair> *sized_list, Output *output) -> void {
	helper(sized_list->len, sized_list->list, output);
}
