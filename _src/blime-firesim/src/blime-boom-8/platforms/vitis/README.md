
Running make replace-rtl PLATFORM=vitis from firesim will copy cl_firesim into a secondary directory
and populate it with the necessary sources. We'll call this subdirectory, WORKDIR.

# Bitstream Builds

`make bitstream` to build an XCLBIN that can be deployed to a U250. Bitstream builds run under the $WORDIR/bitstream

# FPGA-level Metasimulation

`make sim` to build a XCLBIN that can be deployed as an FPGA\_level metasimulator (hardware emulation in Vitis parlance). Most generated
files are found under $WORKDIR/simulation.

`make run-sim` to run metasimulation using rv64ui-p-simple. The simulator is launched under $WORKDIR/simulation/*.run/

# Debugging Failing Vitis Builds

The vitis compiler (v++) can be fairly opaque due to multiple layers of TCL
wrapping which abstract the underlying calls to Vivado.

A typical v++ linking log may appear as follows:
[12:50:32] Run vpl: Step create_bd: Started
[12:51:15] Run vpl: Step create_bd: Completed
[12:51:15] Run vpl: Step update_bd: Started
[12:51:16] Run vpl: Step update_bd: Completed
[12:51:16] Run vpl: Step generate_target: Started
[12:54:58] Run vpl: Step generate_target: Completed
[12:54:58] Run vpl: Step config_hw_runs: Started
[12:56:01] Run vpl: Step config_hw_runs: Completed
[12:56:01] Run vpl: Step synth: Started
[12:56:32] Block-level synthesis in progress, 0 of 250 jobs complete, 1 job running.
...
[13:08:05] Top-level synthesis in progress.
...
[13:09:49] Run vpl: Step synth: Completed
[13:09:49] Run vpl: Step impl: Started

Xilinx gives an overview of the generated directory structure
[here](https://www.xilinx.com/html_docs/xilinx2021_1/vitis_doc/output_dir.html),
but does not describe the files themselves. Intermediate outputs are stored at
location specified by v++'s --temp_dir command-line argument. We'll call this `$TEMP`.

## Linking
Most of the interesting work for Linking is done under $TEMP/link/vivado/vpl,
with a generated Vivado project found under `prj/`.  If you're familiar with a
project-based Vivado flow, you'll know roughly where to look for things.
Here's an overview of this subdirectory:

open\_prj.tcl -- Script to reopen the vivado project after an attempted lin
prj/ -- root of generated vivado project
   prj.xpr -- the project itself
   prj.srcs/
   prj.runs/ -- outputs from various vivado steps. See runme.log in each subdir output.
        <many_block_level_synth_runs> --  the outer project uses at ton of IP blocks
        my_rm_synth_1/ -- Final block-level synthesis run?
        ulp_firesim_1_0_synth_1 -- Synthesis of FireSim verilog contained here.
        impl_<N>/ -- Output from link_design, opt_design, implementation contained here



This project can be re-opened interactively using
cd $BUILD/vivado/vpl/
vivado -source openprj.tcl
