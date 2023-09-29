BliMe gem5 simulations
======================

Note: This entire experiment requires approximately 180GB of disk space.

    Install prerequisites:

    sudo apt install build-essential git m4 scons zlib1g zlib1g-dev libprotobuf-dev protobuf-compiler libprotoc-dev libgoogle-perftools-dev python-dev python


Build gem5 in all repos:
```console
$ cd blinded-gem5-opt
$ python3 `which scons` build/RISCV/gem5.opt -j9
$ cd ../blinded-gem5-unopt
$ python3 `which scons` build/RISCV/gem5.opt -j9
$ cd ../baseline-gem5
$ python3 `which scons` build/RISCV/gem5.opt -j9
4 cd ..
```

Copy custom RISC-V Linux image containing SPEC CPU17 into gem5-experiments/

Run experiments:

```console 
cd gem5-experiments
./do_ucanlinux_experiment.sh ../blinded-gem5-opt riscv-disk-mod-new.img run_ucanlinux.py mod
```

Once all benchmarks have been run (tmux sessions stop spawning), clear the terminal:

```console 
 reset
```

Repeat for blinded-gem5-unopt and baseline-gem5:

```console 
 ./do_ucanlinux_experiment.sh ../blinded-gem5-unopt riscv-disk-mod-new.img run_ucanlinux-blinded-unopt.py base
 ./do_ucanlinux_experiment.sh ../baseline-gem5 riscv-disk-mod-new.img run_ucanlinux.py base
```

Get results by running this in the 'benchmarks' folder of each experiment:

```console 
find . -wholename '*/m5out/stats.txt' | xargs grep 'core.ipc'
```

This will print out the instructions per cycle (IPC) twice for each benchmark. The first value can be ignored since it corresponds to output before the benchmark is run. The second value is the one that should be used.
