BliMe gem5 simulations
======================

This README describes the gem5 experiments for BliMe. The goal is to run SPEC CPU 2017 on gem5. Running all the benchmarks to completion is infeasibly long. Therefore, for each benchmark, we run 10B warm-up instructions and then run and measure the instructions per cycle (IPC) for the next 1B instructions. We spawn two tmux sessions per benchmark: one to run gem5, and one to run the benchmark inside gem5.

Note: This entire experiment requires approximately 180GB of disk space.

Install prerequisites:

```console
$ sudo apt install build-essential git m4 scons zlib1g zlib1g-dev libprotobuf-dev protobuf-compiler libprotoc-dev libgoogle-perftools-dev python-dev python
```

Fetch submodules:
```console
$ git submodule update --init blime-gem5-baseline blime-gem5-experiments blime-gem5-opt blime-gem5-unopt
```

Build gem5 in all repos:
```console
$ cd blime-gem5-opt
$ python3 `which scons` build/RISCV/gem5.opt -j9
$ cd ../blime-gem5-unopt
$ python3 `which scons` build/RISCV/gem5.opt -j9
$ cd ../blime-gem5-baseline
$ python3 `which scons` build/RISCV/gem5.opt -j9
$ cd ..
```

Copy custom RISC-V Linux image containing SPEC CPU17 to `blime-gem5-experiments/riscv-disk-mod-new.img`

Run experiments:

```console 
$ cd blime-gem5-experiments
$ ./do_ucanlinux_experiment.sh ../blime-gem5-opt riscv-disk-mod-new.img run_ucanlinux.py mod
```

Once all benchmarks have been run (tmux sessions stop spawning), clear the terminal:

```console
$ reset
```

Repeat for `blime-gem5-unopt` and `blime-gem5-baseline`:

```console 
$ ./do_ucanlinux_experiment.sh ../blime-gem5-unopt riscv-disk-mod-new.img run_ucanlinux-blinded-unopt.py base
$ ./do_ucanlinux_experiment.sh ../blime-gem5-baseline riscv-disk-mod-new.img run_ucanlinux.py base
```

Get results by running this in the 'benchmarks' folder of each experiment:

```console 
$ find . -wholename '*/m5out/stats.txt' | xargs grep 'core.ipc'
```

This will print out the instructions per cycle (IPC) twice for each benchmark. The first value can be ignored since it corresponds to output before the benchmark is run. The second value is the one that should be used. An example output is shown below:

```console
./505.mcf_r/m5out/stats.txt:board.processor.cores.core.ipc               0.687457                       # IPC: Instructions Per Cycle ((Count/Cycle))
./505.mcf_r/m5out/stats.txt:board.processor.cores.core.ipc               1.330130                       # IPC: Instructions Per Cycle ((Count/Cycle))
./525.x264_r/m5out/stats.txt:board.processor.cores.core.ipc               0.670396                       # IPC: Instructions Per Cycle ((Count/Cycle))
./525.x264_r/m5out/stats.txt:board.processor.cores.core.ipc               1.214056                       # IPC: Instructions Per Cycle ((Count/Cycle))
./502.gcc_r/m5out/stats.txt:board.processor.cores.core.ipc               0.615172                       # IPC: Instructions Per Cycle ((Count/Cycle))
./502.gcc_r/m5out/stats.txt:board.processor.cores.core.ipc               0.864051                       # IPC: Instructions Per Cycle ((Count/Cycle))
./523.xalancbmk_r/m5out/stats.txt:board.processor.cores.core.ipc               0.629060                       # IPC: Instructions Per Cycle ((Count/Cycle))
./523.xalancbmk_r/m5out/stats.txt:board.processor.cores.core.ipc               0.538762                       # IPC: Instructions Per Cycle ((Count/Cycle))
./531.deepsjeng_r/m5out/stats.txt:board.processor.cores.core.ipc               0.497763                       # IPC: Instructions Per Cycle ((Count/Cycle))
./531.deepsjeng_r/m5out/stats.txt:board.processor.cores.core.ipc               0.477020                       # IPC: Instructions Per Cycle ((Count/Cycle))
./557.xz_r/m5out/stats.txt:board.processor.cores.core.ipc               0.406067                       # IPC: Instructions Per Cycle ((Count/Cycle))
./557.xz_r/m5out/stats.txt:board.processor.cores.core.ipc               0.384899                       # IPC: Instructions Per Cycle ((Count/Cycle))
./520.omnetpp_r/m5out/stats.txt:board.processor.cores.core.ipc               0.591440                       # IPC: Instructions Per Cycle ((Count/Cycle))
./520.omnetpp_r/m5out/stats.txt:board.processor.cores.core.ipc               0.515349                       # IPC: Instructions Per Cycle ((Count/Cycle))
./541.leela_r/m5out/stats.txt:board.processor.cores.core.ipc               0.715762                       # IPC: Instructions Per Cycle ((Count/Cycle))
./541.leela_r/m5out/stats.txt:board.processor.cores.core.ipc               3.156542                       # IPC: Instructions Per Cycle ((Count/Cycle))
./548.exchange2_r/m5out/stats.txt:board.processor.cores.core.ipc               0.765990                       # IPC: Instructions Per Cycle ((Count/Cycle))
./548.exchange2_r/m5out/stats.txt:board.processor.cores.core.ipc               3.020920                       # IPC: Instructions Per Cycle ((Count/Cycle))
./500.perlbench_r/m5out/stats.txt:board.processor.cores.core.ipc               0.390491                       # IPC: Instructions Per Cycle ((Count/Cycle))
./500.perlbench_r/m5out/stats.txt:board.processor.cores.core.ipc               1.256578                       # IPC: Instructions Per Cycle ((Count/Cycle))
```

In the case above, the correct IPC for the `505.mcf_r` benchmark would be `1.330130`.