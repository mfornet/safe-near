#!/usr/bin/env python3
"""Regenerate the raw bundles of one topology: init, start, workload, stop, export (stdlib only).

    python3 tools/localnet/generate.py single|sharded [--seed N]

Needs the binaries of ``build.py``.  Output: ``data/TOPOLOGY/raw/hHEIGHT-sSHARD/bundle.json`` plus
``data/TOPOLOGY/workload.json``; ``corpus.py pack`` turns the bundles into corpus chunks.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys

import localnet
import workload


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("topology", choices=sorted(localnet.TOPOLOGIES))
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--keep-running", action="store_true")
    arguments = parser.parse_args()
    topology = arguments.topology
    localnet.stop(topology)
    localnet.init(topology)
    localnet.start(topology)
    try:
        localnet.wait_ready(topology)
        plan = workload.Workload(workload.Net(topology), arguments.seed)
        try:
            plan.run_all()
        finally:
            last = plan.net.height()
            log = localnet.home(topology) / "workload.json"
            log.write_text(json.dumps({"topology": topology, "seed": arguments.seed, "lastHeight": last,
                                       "transactions": plan.log}, indent=1))
    finally:
        if not arguments.keep_running:
            localnet.stop(topology)
    raw = localnet.home(topology) / "raw"
    shutil.rmtree(raw, ignore_errors=True)
    subprocess.run([str(localnet.BIN / "safe-near-corpus-export"), "--home", str(localnet.home(topology) / "node0"),
                    "--out", str(raw), "--from", "1", "--to", str(last)], check=True)
    print(f"raw bundles in {raw}")


if __name__ == "__main__":
    main()
