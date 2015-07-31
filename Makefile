default: run

benchmark:
	ghc -O2 benchmark

run: benchmark
	echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost

.PHONY: benchmark run
