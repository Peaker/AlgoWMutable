default: run

benchmark:
	ghc -O2 benchmark

benchmark.p.prof: benchmark.p
	./$< +RTS -p

benchmark.p:
	ghc -O2 -o benchmark.p --make benchmark.hs -hisuf .p_hi -osuf .p_o -prof -caf-all

run: benchmark
	echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost

runboosted: benchmark
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<

.PHONY: benchmark benchmark.p benchmark.p.prof run
