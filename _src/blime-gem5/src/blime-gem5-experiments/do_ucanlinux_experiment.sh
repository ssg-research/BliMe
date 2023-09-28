#!/bin/bash

usage(){
	echo "Usage: $0 <gem5-root-dir> <disk-image> <gem5-config-pyfile> <experiment-tag>"
	echo "gem5-config-pyfile must take disk-image path as an --diskimg argument"
	exit 1
}

[[ $# -lt 4 ]] && usage

GEM5_ROOTDIR=$(realpath -e $1)
DISK_IMG=$(realpath -e $2)
GEM5_CONFIG=$(realpath -e $3)
EXP_TAG=$4
echo "Experiment tag: " ${EXP_TAG}

EXP_DIR=experiment_${EXP_TAG}
BENCHMARK_LIST=(500.perlbench_r 502.gcc_r 505.mcf_r 520.omnetpp_r 523.xalancbmk_r 525.x264_r 531.deepsjeng_r 541.leela_r 548.exchange2_r 557.xz_r)
TMUX_LIST=(500_perlbench 502_gcc 505_mcf 520_omnetpp 523_xalancbmk 525_x264 531_deepsjeng 541_leela 548_exchange2 557_xz)
# BENCHMARK_LIST=(541.leela_r)
# TMUX_LIST=(541_leela)


# clean everything
rm -rf ${EXP_DIR}

mkdir ${EXP_DIR}
mkdir ${EXP_DIR}/benchmarks
cp -pr ${GEM5_ROOTDIR} ${EXP_DIR}/gem5
cp -p ${GEM5_CONFIG} ${EXP_DIR}/gem5/gem5_config.py
cp -p ${DISK_IMG} ${EXP_DIR}/riscv-auto-disk.img
cd ${EXP_DIR}
rm -f gem5/*.img
rm -rf gem5/build/X86

for bmark_name in "${BENCHMARK_LIST[@]}"; do 
    cp -pr gem5 benchmarks/$bmark_name
done

for i in "${!BENCHMARK_LIST[@]}"; do 
	tmux_name="${TMUX_LIST[$i]}"
	tmux_run=${EXP_TAG}_run_${tmux_name}
	tmux_telnet=${EXP_TAG}_telnet_${tmux_name}
	bmark_name="${BENCHMARK_LIST[$i]}"

	cd benchmarks/${bmark_name}
	tmux kill-session -t ${tmux_run}
	tmux kill-session -t ${tmux_telnet}

	../../../tmux-gem5.expect ${tmux_run} "gem5_config.py" "../../riscv-auto-disk.img" &
	tmux new-session -d -t ${tmux_telnet}
	sleep 10;

	port_number=$(cat port_number)
	if [ -z "$port_number" ]; then
		echo "port number not set!"
    	exit 1;
	fi
	tmux send -t ${tmux_telnet} ../../../ucanlinux-telnet.expect SPACE ${port_number} SPACE "/helatali/SPEC/installdir2/benchspec/CPU/${bmark_name}/run/run_base_refrate_riscv-64.0000/runMe-print.sh" ENTER
	cd ../..


	
done