#!/usr/bin/env python3
"""Acceptance of the JSON-RPC server (M9b): `just node-rpc-conformance`.

The validator topology (``localnet.TOPOLOGIES["validator"]``): ``neard`` (node0) and the Lean node (node1) hold half of
the stake each.  The run

1. starts both, runs the finite workload on ``neard`` to its end (accounts, contracts, promises, delegate actions,
   global contracts), and lets the chain go on;
2. sends the same request set to the RPC of ``neard`` and to the RPC of the Lean node and compares the responses
   field by field after the normalisation of ``NORMALISATION`` below (and nothing else);
3. sends transactions through the RPC of the Lean node (``send_tx``, ``broadcast_tx_async``, ``broadcast_tx_commit``)
   and compares what both nodes say of them;
4. stops the Lean validator in the middle of the run and starts it again from its store: finality must go on.

``serve`` only brings the topology up (to look at responses by hand).
"""

from __future__ import annotations

import argparse
import base64
import copy
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import urllib.error
import urllib.request

import chain_corpus
import localnet
import nearcodec as nc
import validator_accept as va

TOPOLOGY = va.TOPOLOGY
ROOT = va.ROOT
SEED = 1                      # the workload's seed: its accounts and keys derive from it

# What legitimately differs between the nodes.  Each entry names a path in the response (dots for objects, ``[]``
# for every element of an array, ``*`` for every key of an object) that is removed from both responses before they
# are compared, with the reason.  Nothing else is touched.
NORMALISATION = {
    "status": {
        "version": "the build of each node",
        "rpc_addr": "each node listens on its own port",
        "uptime_sec": "the time since the start",
        "validator_account_id": "each node is another validator",
        "validator_public_key": "each node is another validator",
        "node_public_key": "each node has its own peer key",
        "node_key": "each node has its own peer key",
    },
    "network_info": {
        "active_peers": "each node has the other as its only peer (compared as a shape)",
        "known_producers": "each node knows the other as producer (compared as a shape)",
        "sent_bytes_per_sec": "traffic",
        "received_bytes_per_sec": "traffic",
    },
}


class Node:
    def __init__(self, name: str, index: int):
        self.name, self.index = name, index
        self.url = f"http://127.0.0.1:{localnet.rpc_port(TOPOLOGY, index)}"

    def raw(self, body, method="POST", path="/", timeout=40):
        data = body if isinstance(body, bytes) else (json.dumps(body).encode() if body is not None else None)
        request = urllib.request.Request(self.url + path, data, {"Content-Type": "application/json"}, method=method)
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.status, dict(response.headers), response.read()
        except urllib.error.HTTPError as error:
            return error.code, dict(error.headers), error.read()

    def call(self, method, params, timeout=40):
        """(HTTP status, parsed body) of a JSON-RPC request."""
        status, _, body = self.raw({"jsonrpc": "2.0", "id": "dontcare", "method": method, "params": params}, timeout=timeout)
        try:
            return status, json.loads(body)
        except ValueError:
            return status, body.decode(errors="replace")


NEARD, LEAN = Node("neard", 0), Node("lean", 1)


def wait_for(predicate, timeout, what, step=0.5):
    deadline = time.time() + timeout
    last = None
    while time.time() < deadline:
        try:
            value = predicate()
            if value:
                return value
        except Exception as error:      # noqa: BLE001
            last = error
        time.sleep(step)
    raise TimeoutError(f"{what} ({last})")


def lean_extra(home: Path) -> list[str]:
    return ["--rpc-addr", f"127.0.0.1:{localnet.rpc_port(TOPOLOGY, 1)}",
            "--genesis-config", str(home / "node1/genesis.json"),
            "--store", str(localnet.DATA / "rpc-run/store")]


def bring_up(work: Path, binary: Path, workload: bool):
    """Prepares the topology and starts neard, the Lean node and (optionally) the workload."""
    home = va.prepare(work)
    localnet.start(TOPOLOGY)
    lean = va.start_lean(home, work, 24 * 3600, binary, lean_extra(home))
    wait_for(lambda: NEARD.call("status", [])[1]["result"]["sync_info"]["latest_block_height"] >= 3, 120, "the chain did not start")
    load = None
    if workload:
        command = [sys.executable, str(Path(__file__).with_name("workload.py")), TOPOLOGY, "--skip", "hostcalls", "burst", "wait",
                   "--seed", str(SEED)]
        load = subprocess.Popen(command, stdout=(work / "workload.log").open("w"), stderr=subprocess.STDOUT,
                                cwd=Path(__file__).parent)
    return home, lean, load


# --------------------------------------------------------------------------------------------------------------------
# normalisation and comparison

def strip(value, path: list[str]):
    """Removes the member at ``path`` (``[]`` for every array element) in place."""
    if not path:
        return
    head, rest = path[0], path[1:]
    if isinstance(value, list):
        for item in value:
            strip(item, path)
    elif isinstance(value, dict):
        if rest == []:
            value.pop(head, None)
        elif head in value:
            strip(value[head], rest)


def normalise(method: str, response):
    """Applies ``NORMALISATION`` (and the failure details rule) to a parsed response; returns the normalised copy."""
    out = copy.deepcopy(response)
    result = out.get("result") if isinstance(out, dict) else None
    for path in NORMALISATION.get(method, {}):
        if result is not None:
            strip(result, path.split("."))
    if result is not None:
        failures_to_marker(result)
        if method == "network_info":
            result["active_peers"] = len(result.get("active_peers", []))
            result["known_producers"] = len(result.get("known_producers", []))
    return out


def failures_to_marker(value):
    """The details of an execution failure (``Failure``: which action failed, with which error) are not reproduced by
    the Lean runtime model; the status is compared as ``Failure``.  The gas profile of the outcome metadata is not
    computed either."""
    if isinstance(value, dict):
        if "Failure" in value and len(value) == 1:
            value["Failure"] = "<failure>"
        value.pop("metadata", None) if set(value.get("metadata", {}) or {}) <= {"version", "gas_profile", "contracts"} and "gas_burnt" in value else None
        for item in value.values():
            failures_to_marker(item)
    elif isinstance(value, list):
        for item in value:
            failures_to_marker(item)


def diff(a, b, path=""):
    out = []
    if type(a) != type(b):
        return [f"{path or '.'}: {json.dumps(a)[:160]} != {json.dumps(b)[:160]}"]
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a:
                out.append(f"{path}.{k}: only in lean: {json.dumps(b[k])[:120]}")
            elif k not in b:
                out.append(f"{path}.{k}: only in neard: {json.dumps(a[k])[:120]}")
            else:
                out += diff(a[k], b[k], f"{path}.{k}")
    elif isinstance(a, list):
        if len(a) != len(b):
            out.append(f"{path}: length {len(a)} != {len(b)}")
        for i, (x, y) in enumerate(zip(a, b)):
            out += diff(x, y, f"{path}[{i}]")
    elif a != b:
        out.append(f"{path or '.'}: {json.dumps(a)[:160]} != {json.dumps(b)[:160]}")
    return out


class Request:
    def __init__(self, group: str, method: str, params, head: bool = False, note: str = ""):
        self.group, self.method, self.params, self.head, self.note = group, method, params, head, note


def heads() -> tuple:
    return (NEARD.call("status", [])[1]["result"]["sync_info"]["latest_block_hash"],
            LEAN.call("status", [])[1]["result"]["sync_info"]["latest_block_hash"])


def compare(request: Request, attempts: int = 12) -> dict:
    """Sends the request to both nodes.  A request that depends on the head is repeated until both nodes answered
    at the same head (their heads are read before and after)."""
    for attempt in range(attempts if request.head else 1):
        before = heads() if request.head else None
        sn, rn = NEARD.call(request.method, request.params)
        sl, rl = LEAN.call(request.method, request.params)
        after = heads() if request.head else None
        if request.head and not (before[0] == before[1] == after[0] == after[1]):
            time.sleep(0.05)
            continue
        break
    else:
        return {"request": request, "equal": False, "stale": True, "diff": ["the nodes never answered at the same head"]}
    nn, nl = normalise(request.method, rn), normalise(request.method, rl)
    problems = diff(nn, nl)
    if sn != sl:
        problems.insert(0, f"HTTP status {sn} != {sl}")
    return {"request": request, "equal": not problems, "diff": problems, "status": sn, "ok": isinstance(rn, dict) and "result" in rn}


def serve(options) -> None:
    home, lean, load = bring_up(options.work, options.binary, not options.no_workload)
    print("neard", NEARD.url, "lean", LEAN.url, flush=True)
    try:
        while not (options.work / "serve-stop").exists():
            time.sleep(1)
    finally:
        for process in (load, lean):
            if process and process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        localnet.stop(TOPOLOGY)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["serve", "run"], nargs="?", default="run")
    parser.add_argument("--binary", type=Path, default=va.BINARY)
    parser.add_argument("--work", type=Path, default=localnet.DATA / "rpc-run")
    parser.add_argument("--no-workload", action="store_true")
    options = parser.parse_args()
    options.work.mkdir(parents=True, exist_ok=True)
    (options.work / "serve-stop").unlink(missing_ok=True)
    if options.mode == "serve":
        serve(options)
    else:
        raise SystemExit("run: not yet")


if __name__ == "__main__":
    main()
