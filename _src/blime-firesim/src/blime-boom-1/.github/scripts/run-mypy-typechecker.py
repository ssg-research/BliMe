#!/usr/bin/env python3

from fabric.api import *

from common import manager_fsim_dir, set_fabric_firesim_pem

def run_typecheck():
    """Runs mypy typecheck."""

    with cd(manager_fsim_dir), prefix('source env.sh'):
        run("./scripts/run-py-typecheck.sh")

if __name__ == "__main__":
    set_fabric_firesim_pem()
    execute(run_typecheck, hosts=["localhost"])
