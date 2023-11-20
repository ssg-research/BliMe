BliMe FireSim simulations
=========================

This page describes how to build BliMe-BOOM-1 and BliMe-BOOM-8 using FireSim on AWS, and then run the SPEC CPU 2017 benchmarks on them. Power and resource usage overheads can be obtained after the build step (without needing to run SPEC). **Note that running the SPEC CPU 2017 benchmarks to completion on FireSim can cost around $5000 in AWS costs.**

If you are using our provided AWS instance, please skip to step 4.

1. Follow the steps in 1.1 and 1.2 to setup AWS account for first-time access: https://docs.fires.im/en/1.16.0/Initial-Setup/index.html

	- install "python3-pip" instead of "python36-pip"

1. Follow instructions at: https://docs.fires.im/en/1.16.0/Initial-Setup/Setting-up-your-Manager-Instance.html

	- use `FPGA Developer AMI - 1.12.2-40257ab5-6688-4c95-97d1-e251a40fd1fc` instead of what's there

	- for step 8.2, instead of using the provided text, use the contents in: https://github.com/ssg-research/BliMe-firesim/blob/65b19133bf9a07c0bc211a54b3123b8e48f8d9d5/scripts/machine-launch-script.sh

1. copy the `firesim.pem` key to the home directory at `/home/centos`

1. use mosh to login to instance. Clone the `BliMe-firesim` repo and checkout the `blime-baseline`, `blinded-comp` or `blinded-multiclient` branch. Alternatively, fetch the submodules in this directory and copy the corresponding folder to the instance's home directory.

	- if cloning the BliMe-firesim repo, clone it to a folder called "firesim" instead of the default "BliMe-firesim"
	- repeat all the following steps for the 3 branches (`blime-baseline`, `blinded-comp`, `blinded-multiclient`) to get results for the baseline, BliMe-BOOM-1 and BliMe-BOOM-8, respectively. For each branch, delete the `/home/centos/firesim` directory if it exists and replace it with the new one.	
	- **Known Issue: do not recursively clone all submodules**. Use a shallow clone, e.g.: `git clone https://github.com/ssg-research/BliMe-firesim.git firesim`. The `build-setup.sh` script in the following step will fetch the appropriate submodules.
	
1. in the `firesim` folder, run `./build-setup.sh`

	- enter "y" when asked about being on an unofficial branch

1. run the following:

	```bash
	source sourceme-f1-manager.sh
	firesim managerinit --platform f1
	```
	- when prompted, use the values in firesim.csv and your email

1. copy the 3 `config_*.yaml` files from the root firesim folder to `deploy/`.

1. run `firesim buildbitstream`. This can take 4-6 hours to complete!
	- when this completes, the power, timing and resource usage reports will be available in `firesim/deploy/results-build/\<timestamp-config\>/\<design\>/build/reports/`. Continue the following steps ONLY if you would like to obtain the SPEC17 benchmark results (at much higher AWS costs)
		- power & resource usage -> `.../reports/\<timestamp\>.SH_CL_final_power.rpt` under "Total On-Chip Power" & "On-Chip Components"
		- timing -> `.../reports/\<timestamp\>.SH_CL_final_timing_summary.rpt` under "WNS(ns)"
	- when it's done (you'll get notified by email), copy the entry sent in the email to deploy/config_hwdb.yaml
	- you can continue with the SPEC installation step below in a separate shell

1. install SPEC 2017 as follows:
	- copy SPEC cpu2017 iso file to instance's home directory
	- run the following:
		```bash
		sudo yum install gcc-gfortran
		mkdir ~/specmount
		sudo mount -o loop <iso-file> ~/specmount
		cd ~/specmount
		./install.sh -d ~/cpu2017
		```
	- if this was done in a separate shell, you can now close it

1. when `firesim buildbitstream` and the SPEC installation steps are both complete, run the following:
	```bash
	export SPEC_DIR=/home/centos/cpu2017
	cd ~/firesim/sw/firesim-software
	./init-submodules.sh
	cd ~/firesim/target-design/chipyard/software
	git submodule update --init --recursive spec2017
	cd spec2017
	sed -i -e 's/ --copies 4//g' ./marshal-configs/spec17-intrate.json
	marshal build ./marshal-configs/spec17-intrate.json
	marshal install ./marshal-configs/spec17-intrate.json
	cd ~/firesim
	firesim launchrunfarm
	firesim infrasetup
	firesim runworkload
	```

1. **IMPORTANT** once all the simulations are done, run `firesim terminaterunfarm` and enter "yes"
	- this terminates the f1 instances, which are the highest contributor to cost

1. the benchmark results will be found in `deploy/results-workload/<timestamp>-spec17-intrate/results.csv`
