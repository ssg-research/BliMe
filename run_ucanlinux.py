# Copyright (c) 2021 The Regents of the University of California
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met: redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer;
# redistributions in binary form must reproduce the above copyright
# notice, this list of conditions and the following disclaimer in the
# documentation and/or other materials provided with the distribution;
# neither the name of the copyright holders nor the names of its
# contributors may be used to endorse or promote products derived from
# this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""
This script shows an example of running a full system RISCV Ubuntu boot
simulation using the gem5 library. This simulation boots Ubuntu 20.04 using
2 TIMING CPU cores. The simulation ends when the startup is completed
successfully.

Usage
-----

```
scons build/RISCV/gem5.opt
./build/RISCV/gem5.opt \
    configs/example/gem5_library/riscv-ubuntu-run.py
```
"""

import argparse
from pathlib import Path
import os
from datetime import datetime

import m5
from m5.objects import Root

from gem5.utils.requires import requires
from gem5.components.boards.riscv_board import RiscvBoard
from gem5.components.memory import DualChannelDDR4_2400, SingleChannelDDR4_2400, DualChannelDDR3_1600, SingleChannelDDR3_1600
from gem5.components.processors.simple_processor import (
    SimpleProcessor,
)
from gem5.components.processors.simple_switchable_processor import(
    SimpleSwitchableProcessor,
)
from gem5.components.processors.cpu_types import CPUTypes
from gem5.isas import ISA
from gem5.coherence_protocol import CoherenceProtocol
from gem5.resources.resource import Resource, CustomDiskImageResource
from gem5.simulate.simulator import Simulator
from gem5.simulate.exit_event import ExitEvent

# This runs a check to ensure the gem5 binary is compiled for RISCV.

requires(
    isa_required=ISA.RISCV,
)

parser = argparse.ArgumentParser(
    description="A config script to run ucanlinux on RISC-V."
)

parser.add_argument(
    "--diskimg",
    type=Path,
    required=True,
    help="Path to disk image."
)

args = parser.parse_args()

# With RISCV, we use simple caches.
from gem5.components.cachehierarchies.classic\
    .private_l1_private_l2_cache_hierarchy import (
    PrivateL1PrivateL2CacheHierarchy,
)
# Here we setup the parameters of the l1 and l2 caches.
cache_hierarchy = PrivateL1PrivateL2CacheHierarchy(
    l1d_size="16kB",
    l1i_size="16kB",
    l2_size="256kB",
)

# Memory: Dual Channel DDR4 2400 DRAM device.

memory = DualChannelDDR3_1600(size = "8GB") # FIXED! DO NOT CHANGE!

# Here we setup the processor. We use a simple processor.
processor = SimpleProcessor(
    # cpu_type=CPUTypes.TIMING,
    cpu_type=CPUTypes.O3,
    # cpu_type=CPUTypes.ATOMIC,
# processor = SimpleSwitchableProcessor(
#     starting_core_type=CPUTypes.ATOMIC,
#     switch_core_type=CPUTypes.O3,
    isa=ISA.RISCV,
    num_cores=1,
)

# Here we setup the board. The RiscvBoard allows for Full-System RISCV
# simulations.
board = RiscvBoard(
    clk_freq="3GHz",
    processor=processor,
    memory=memory,
    cache_hierarchy=cache_hierarchy,
)

# Here we set the Full System workload.

# The `set_kernel_disk_workload` function for the RiscvBoard accepts a
# RISCV bootloader and a disk image. Once the system successfully boots, it
# encounters an `m5_exit instruction encountered`. We stop the simulation then.
# When the simulation has ended you may inspect `m5out/system.pc.com_1.device`
# to see the stdout.

# command = "echo hi;"
        # + "m5 exit;"
        # + "m5 checkpoint;" \
        # + "sleep 1;" \
        # + "m5 exit;"

board.set_kernel_disk_workload(
    # The RISCV bootloader will be automatically downloaded to the
    # `~/.cache/gem5` directory if not already present.
    # The riscv-ubuntu boot-test was tested with riscv-bootloader-5.10
    kernel=Resource(
        "riscv-bootloader-vmlinux-5.10",
    ),
    # The RISCV ubuntu image will be automatically downloaded to the
    # `~/.cache/gem5` directory if not already present.
    disk_image=CustomDiskImageResource(
        # "riscv-ubuntu-20.04-img",
        # local_path = "riscv-disk-img-mod.img",
        local_path = args.diskimg,
        # local_path = "riscv-ubuntu-20.04-mod.img",
        # disk_root_partition = "1"
    )
    # readfile_contents=command,
    # readfile="configs/boot/hack_back_ckpt.rcS"
)



def beginWork():
    print(str(datetime.now()) + "Begin work area!")
    # os.system("rm -rf m5out")
    m5.stats.reset()
    processor.cores[0].core.scheduleInstStop(0, 10000000000, "a thread reached the max instruction count")
    # processor.get_cores()[0].get_simobject().max_insts_any_thread = 100
    print(str(datetime.now()) + "Set max instruction count for warmup")

def dumpNSaveEarlyExit():
    print(str(datetime.now()) + "dumpNSaveEarlyExit")
    m5.stats.dump()
    os.system("rm -rf m5out_copy_earlyexit")
    os.system("cp -pr m5out m5out_copy_earlyexit")

def dumpNSaveAfter10Billion():
    print(str(datetime.now()) + "dumpNSaveAfter10Billion")
    m5.stats.dump()
    os.system("rm -rf m5out_copy10B")
    os.system("cp -pr m5out m5out_copy10B")

def dumpNSave():
    print(str(datetime.now()) + "dumpNSave")
    m5.stats.dump()
    os.system("rm -rf m5out_copy")
    os.system("cp -pr m5out m5out_copy")

# def switchcpu_exit_event():
#     processor.switch()
#     yield False
#     yield True

# def workbegin_exit_event():
#     beginWork()
#     yield False
#     yield True

# def workend_exit_event():
#     dumpNSaveEarly()
#     yield True

def custom_exit_event():
    # processor.switch()
    print(str(datetime.now()) + "First exit!")
    yield False
    beginWork()
    yield False
    dumpNSaveEarlyExit()
    yield True

def maxtick_exit_event():
    dumpNSaveAfter10Billion()
    # os.system("rm -rf m5out")
    m5.stats.reset()
    processor.cores[0].core.scheduleInstStop(0, 1000000000, "a thread reached the max instruction count")
    # processor.get_cores()[0].get_simobject().max_insts_any_thread = 10
    print(str(datetime.now()) + "Set max instruction count for measurement")
    yield False
    dumpNSave()
    yield True


# checkpoint_path = "riscv-hello-checkpoint/"
simulator = Simulator(
    board=board,
    on_exit_event={
    #     # Here we want override the default behavior for the first m5 exit
    #     # exit event. Instead of exiting the simulator, we just want to
    #     # switch the processor. The 2nd m5 exit after will revert to using
    #     # default behavior where the simulator run will exit.
        # ExitEvent.EXIT : (func() for func in [processor.switch]),
        # ExitEvent.SWITCHCPU : switchcpu_exit_event(),
        # ExitEvent.WORKBEGIN : workbegin_exit_event(),
        # ExitEvent.WORKEND : workend_exit_event(),
        ExitEvent.MAX_TICK : maxtick_exit_event(),
        ExitEvent.EXIT : custom_exit_event(),
        # ExitEvent.EXIT : (func() for func in [m5.stats.reset]),
    },
    # checkpoint_path=checkpoint_path
)


# processor.get_cores()[0].get_simobject().max_insts_any_thread = 10000000000

simulator.run()

print(str(datetime.now()) + "Ignoring exit events competely...")

# print("Taking a checkpoint at", checkpoint_path)
# simulator.save_checkpoint(checkpoint_path)
# print("Checkpoint written.")
# simulator.run()
# processor.get_cores()[0].get_simobject().max_insts_any_thread = 10000000000
# m5.stats.reset()
# processor.get_cores()[0].get_simobject().max_insts_any_thread = 1000000000
# simulator.run()
