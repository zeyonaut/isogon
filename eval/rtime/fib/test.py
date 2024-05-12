import time
from statistics import mean, stdev

num_samples = 100
index_top = 16
num_iterations = 100000

def fib(n): 
	x = 0
	y = 1
	for i in range(n):
		tmp = x
		x = y
		y += tmp
	return x

def bench(sample_count, index_top, num_iterations, ):
	means = []
	stds = []
	for n in range(index_top):
		durations = []
		for s in range(sample_count):
			start = time.monotonic_ns()
			for i in range(num_iterations):
				fib(n)
			end = time.monotonic_ns()
			duration = end - start
			durations.append(duration)
		smean = mean(durations)
		sstd = stdev(durations, smean)
		means.append(smean * 10**-9)
		stds.append(sstd * 10**-9)
	for m, s in zip(means, stds):
		print(m, s, sep=", ")

bench(num_samples, index_top, num_iterations)
