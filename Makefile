default: run

benchmark.O2:
	ghc -O2 -hisuf .O2_hi -osuf .O2_o -o $@ --make benchmark.hs

benchmark.O1:
	ghc -O1 -hisuf .O1_hi -osuf .O1_o -o $@ --make benchmark.hs

benchmark.p.prof: benchmark.p
	./$< +RTS -p

benchmark.p:
	ghc -O1 -o $@ --make benchmark.hs -hisuf .p_hi -osuf .p_o -prof -caf-all

run: benchmark
	echo 0 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost

runboosted: benchmark
	echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost
	./$<

.PHONY: benchmark benchmark.O1 benchmark.O2 benchmark.p benchmark.p.prof run
