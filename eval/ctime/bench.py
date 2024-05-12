import time
from statistics import mean, stdev
import subprocess


program_names = ["unzip", "fib", "pow", "mklist"]

sample_count = 1000

def bench_is(program_name):
    durations = []
    for _ in range(sample_count):
        start = time.monotonic_ns()
        subprocess.run(["../../target/release/isogon",
                       "-f", program_name + ".is", "-q", "-o", "tmp/tmp.o"])
        end = time.monotonic_ns()
        duration = end - start
        durations.append(duration)
    smean = mean(durations)
    sstd = stdev(durations, smean)
    print(program_name + ".is", ": mean = ", smean * 10 ** -9, ", std = ", sstd * 10 ** -9, sep="")
    
def bench_cc(program_name):
    durations = []
    for _ in range(sample_count):
        start = time.monotonic_ns()
        subprocess.run(["clang",
                       "-std=c++20", program_name + ".cc", "-c", "-o", "tmp/tmp.o"])
        end = time.monotonic_ns()
        duration = end - start
        durations.append(duration)
    smean = mean(durations)
    sstd = stdev(durations, smean)
    print(program_name + ".cc", ": mean = ", smean * 10 ** -9, ", std = ", sstd * 10 ** -9, sep="")

for program_name in program_names:
	bench_is(program_name)
	bench_cc(program_name)
