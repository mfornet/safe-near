#!/usr/bin/env python3
"""Create, start and stop the pinned neard localnets (stdlib only).

Two topologies, both at the protocol version of the pinned binary (86):

* ``single``  : 1 validator, 1 shard
* ``sharded`` : 2 validators, 4 shards (boundary accounts test1, test2, test3)

``init`` runs ``neard localnet`` and then pins everything that is random or
clock-dependent in the generated configuration (chain id, genesis time, ports,
garbage collection) so that two runs start from byte-identical homes.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import urllib.request

import build

HERE = Path(__file__).resolve().parent
BIN = HERE / "target/bin"
DATA = HERE / "data"

TOPOLOGIES = {
    "single": {"validators": 1, "shards": 1, "chainId": "safe-near-localnet-1s", "basePort": 18100},
    "sharded": {"validators": 2, "shards": 4, "chainId": "safe-near-localnet-4s", "basePort": 18200},
}
GENESIS_TIME = "2026-01-01T00:00:00.000000000Z"
EPOCH_LENGTH = 30
TRANSACTION_VALIDITY_PERIOD = 60


def home(topology: str) -> Path:
    return DATA / topology


def rpc_port(topology: str, index: int) -> int:
    return TOPOLOGIES[topology]["basePort"] + 2 * index


def network_port(topology: str, index: int) -> int:
    return TOPOLOGIES[topology]["basePort"] + 2 * index + 1


def init(topology: str) -> Path:
    spec = TOPOLOGIES[topology]
    root = home(topology)
    if root.exists():
        shutil.rmtree(root)
    root.mkdir(parents=True)
    subprocess.run([str(BIN / "neard"), "--home", str(root), "localnet", "-v", str(spec["validators"]),
                    "-s", str(spec["shards"]), "--prefix", "node"], check=True, env=build.neard_environment(BIN),
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    boot_key = None
    for index in range(spec["validators"]):
        node = root / f"node{index}"
        key = json.loads((node / "node_key.json").read_text())
        if index == 0:
            boot_key = key["public_key"]
        config = json.loads((node / "config.json").read_text())
        config["rpc"]["addr"] = f"127.0.0.1:{rpc_port(topology, index)}"
        config["network"]["addr"] = f"127.0.0.1:{network_port(topology, index)}"
        config["network"]["public_addrs"] = [f"{key['public_key']}@127.0.0.1:{network_port(topology, index)}"]
        config["network"]["boot_nodes"] = "" if index == 0 else f"{boot_key}@127.0.0.1:{network_port(topology, 0)}"
        # Keep the whole history: the exporter reads it after the run.
        config["gc_num_epochs_to_keep"] = 10_000   # GCConfig is flattened into config.json
        (node / "config.json").write_text(json.dumps(config, indent=2, sort_keys=True) + "\n")
        genesis = json.loads((node / "genesis.json").read_text())
        genesis["chain_id"] = spec["chainId"]
        genesis["genesis_time"] = GENESIS_TIME
        genesis["epoch_length"] = EPOCH_LENGTH
        genesis["transaction_validity_period"] = TRANSACTION_VALIDITY_PERIOD
        (node / "genesis.json").write_text(json.dumps(genesis, indent=2) + "\n")
    return root


def start(topology: str) -> list[int]:
    spec = TOPOLOGIES[topology]
    root = home(topology)
    pids = []
    for index in range(spec["validators"]):
        node = root / f"node{index}"
        log = (node / "neard.log").open("ab")
        env = dict(build.neard_environment(BIN), RUST_LOG="warn")
        process = subprocess.Popen([str(BIN / "neard"), "--home", str(node), "run"], stdout=log, stderr=log,
                                   env=env, start_new_session=True)
        (node / "neard.pid").write_text(str(process.pid))
        pids.append(process.pid)
    return pids


def stop(topology: str) -> None:
    root = home(topology)
    for pid_file in sorted(root.glob("node*/neard.pid")):
        try:
            pid = int(pid_file.read_text())
            os.killpg(pid, signal.SIGTERM)
        except (ProcessLookupError, ValueError):
            pass
        pid_file.unlink(missing_ok=True)
    deadline = time.time() + 60
    while time.time() < deadline:
        if subprocess.run(["pgrep", "-f", f"--home {root}"], capture_output=True).returncode != 0:
            return
        time.sleep(1)
    subprocess.run(["pkill", "-9", "-f", f"--home {root}"])


def rpc(topology: str, method: str, params, index: int = 0, timeout: float = 30):
    body = json.dumps({"jsonrpc": "2.0", "id": "x", "method": method, "params": params}).encode()
    request = urllib.request.Request(f"http://127.0.0.1:{rpc_port(topology, index)}", body,
                                     {"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return json.load(response)


def wait_ready(topology: str, timeout: float = 180) -> None:
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            status = rpc(topology, "status", [], timeout=5)["result"]
            if status["sync_info"]["latest_block_height"] > 3 and not status["sync_info"]["syncing"]:
                return
        except Exception:
            pass
        time.sleep(1)
    raise TimeoutError("localnet did not become ready")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["init", "start", "stop", "status"])
    parser.add_argument("topology", choices=sorted(TOPOLOGIES))
    arguments = parser.parse_args()
    if arguments.action == "init":
        print(init(arguments.topology))
    elif arguments.action == "start":
        print(start(arguments.topology))
        wait_ready(arguments.topology)
    elif arguments.action == "stop":
        stop(arguments.topology)
    else:
        print(json.dumps(rpc(arguments.topology, "status", [])["result"]["sync_info"], indent=2))


if __name__ == "__main__":
    main()
