import time

def fib(n): 
	x = 0
	y = 1
	for i in range(n):
		tmp = x
		x = y
		y += tmp
	return x

def bench(num_iterations, top):
	start = time.monotonic()
	for i in range(num_iterations):
		for n in range(top):
			fib(n)
	end = time.monotonic()
	return end - start

print(bench(100000, 10))