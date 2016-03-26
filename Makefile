GHC=ghc -o "$@" -itest

default: run

test/benchmark.O2:
	${GHC} -O2 -hisuf .O2.hi -osuf .O2.o test/benchmark.hs

test/benchmark.O1:
	${GHC} -O1 -hisuf .O1.hi -osuf .O1.o test/benchmark.hs

test/benchmark.p.prof: benchmark.p
	./$< +RTS -p

test/benchmark.p:
	${GHC} -O1 test/benchmark.hs -hisuf .p_hi -osuf .p_o -prof -caf-all

run: test/benchmark.O2
	-echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<
	-echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost

runboosted: benchmark
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<

.PHONY: test/{benchmark,benchmark.O1,benchmark.O2,benchmark.p,benchmark.p.prof} run
