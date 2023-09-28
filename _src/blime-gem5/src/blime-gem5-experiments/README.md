Note: This entire experiment requires approximately 180GB of disk space.

1. Install prerequisites:
	```bash
	sudo apt install build-essential git m4 scons zlib1g zlib1g-dev libprotobuf-dev protobuf-compiler libprotoc-dev libgoogle-perftools-dev python-dev python
	```

1. Clone repos:
	```bash
	git clone https://github.com/ssg-research/BliMe-gem5.git blime-gem5-unopt
	git clone https://github.com/ssg-research/BliMe-gem5.git blime-gem5-opt
	git clone https://github.com/ssg-research/BliMe-gem5.git baseline-gem5
	git clone https://github.com/ssg-research/BliMe-gem5-experiments.git
	cd blinded-gem5-opt
	git checkout BliMe-gem5-optimized
	cd ../blinded-gem5-unopt
	git checkout BliMe-gem5-unoptimized
	cd ../baseline-gem5
	git checkout blinded_baseline
	cd ..
	```

1. Build gem5 in all repos:
	```bash
	cd blinded-gem5-opt
	python3 `which scons` build/RISCV/gem5.opt -j9
	cd ../blinded-gem5-unopt
	python3 `which scons` build/RISCV/gem5.opt -j9
	cd ../baseline-gem5
	python3 `which scons` build/RISCV/gem5.opt -j9
	cd ..
	```

1. Copy custom RISC-V Linux image containing SPEC CPU17 into gem5-experiments/

1. Run experiments:
	```bash
	cd gem5-experiments
	./do_ucanlinux_experiment.sh ../blinded-gem5-opt riscv-disk-mod-new.img run_ucanlinux.py mod
	```
	- Once all benchmarks have been run (tmux sessions stop spawning), clear the terminal:
		```bash
		reset
		```
	- Repeat for blinded-gem5-unopt and baseline-gem5:
		```bash
		./do_ucanlinux_experiment.sh ../blinded-gem5-unopt riscv-disk-mod-new.img run_ucanlinux-blinded-unopt.py base
		./do_ucanlinux_experiment.sh ../baseline-gem5 riscv-disk-mod-new.img run_ucanlinux.py base
		```

1. Get results by running this in the 'benchmarks' folder of each experiment:
	```bash
	find . -wholename '*/m5out/stats.txt' | xargs grep 'core.ipc'
	```
	- This will print out the instructions per cycle (IPC) twice for each benchmark. The first value can be ignored since it corresponds to output before the benchmark is run. The second value is the one that should be used.
