GHC=ghc -o "$@" "$<" -itest
O1_FLAGS=-O1 -hisuf .O1.hi -osuf .O1.o
O2_FLAGS=-O2 -hisuf .O2.hi -osuf .O2.o
P_FLAGS=-O2 -hisuf .p_hi -osuf .p_o -prof -caf-all

default: build run

test/benchmark.O2: test/benchmark.hs
	${GHC} ${O2_FLAGS}

test/benchmark.O1: test/benchmark.hs
	${GHC} ${O1_FLAGS}

test/benchmark.p: test/benchmark.hs
	${GHC} ${P_FLAGS}

test/benchmark.p.prof: benchmark.p
	./$< +RTS -p

%.result: %
	"$<" > "$@"

build: test/TestRefZone.O2.result test/InferTests.O2.result

test/InferTests.O2: test/InferTests.hs
	${GHC} ${O2_FLAGS}

test/TestRefZone.O2: test/TestRefZone.hs
	${GHC} ${O2_FLAGS}

run: test/benchmark.O2
	-echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<
	-echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost

runboosted: benchmark
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<

.PHONY: test/{benchmark,benchmark.O1,benchmark.O2,benchmark.p,benchmark.p.prof} run
