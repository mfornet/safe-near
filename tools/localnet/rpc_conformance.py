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
import collections
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


# --gc-epochs-to-keep of the Lean node, only when the command line asks for one (--gc-epochs).  By default the node reads
# `gc_num_epochs_to_keep` from `node1/config.json` (--home), as neard does: `localnet.py` writes 10000 there (the whole history is
# kept for the exporter), and the requests ask for blocks and transactions of the first epochs.
GC_EPOCHS: list[int] = []


def lean_extra(home: Path) -> list[str]:
    return ["--home", str(home / "node1"),
            "--rpc-addr", f"127.0.0.1:{localnet.rpc_port(TOPOLOGY, 1)}",
            "--genesis-config", str(home / "node1/genesis.json"),
            "--store", str(localnet.DATA / "rpc-run/store")] + [x for n in GC_EPOCHS for x in ("--gc-epochs-to-keep", str(n))]


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
        if method == "network_info":
            result["active_peers"] = len(result.get("active_peers", []))
            result["known_producers"] = len(result.get("known_producers", []))
    return out


UNRENDERED = "<unrendered failure>"
UNRENDERED_KINDS: collections.Counter = collections.Counter()


def unify_unrendered(a, b) -> int:
    """A ``Failure`` that the Lean node says it does not render (``UNRENDERED``) is made equal to neard's, and counted;
    every other failure is compared as it is."""
    count = 0
    if isinstance(a, dict) and isinstance(b, dict):
        for k in a:
            if k in b:
                if k == "Failure" and b[k] == UNRENDERED:
                    UNRENDERED_KINDS[json.dumps(a[k])[:150]] += 1
                    a[k] = UNRENDERED
                    count += 1
                else:
                    count += unify_unrendered(a[k], b[k])
    elif isinstance(a, list) and isinstance(b, list):
        for x, y in zip(a, b):
            count += unify_unrendered(x, y)
    return count


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
    unrendered = unify_unrendered(nn, nl)
    problems = diff(nn, nl)
    if sn != sl:
        problems.insert(0, f"HTTP status {sn} != {sl}")
    return {"request": request, "equal": not problems, "diff": problems, "status": sn, "ok": isinstance(rn, dict) and "result" in rn,
            "unrendered": unrendered}


# --------------------------------------------------------------------------------------------------------------------
# the request set

def u64le(n: int) -> bytes:
    return n.to_bytes(8, "little")


def b64(data: bytes) -> str:
    return base64.b64encode(data).decode()


class Chain:
    """What the request set is built from: the chain as neard reports it."""

    def __init__(self):
        self.head = NEARD.call("status", [])[1]["result"]["sync_info"]["latest_block_height"]
        self.blocks: dict[int, dict] = {}
        for height in range(0, self.head + 1):
            status, reply = NEARD.call("block", {"block_id": height})
            if status == 200 and "result" in reply:
                self.blocks[height] = reply["result"]
        self.chunks: dict[str, dict] = {}          # chunk hash -> chunk view
        self.txs: list[dict] = []                  # transaction views with their block height
        for height, block in self.blocks.items():
            for chunk in block["chunks"]:
                if chunk["height_included"] == height and chunk["chunk_hash"] not in self.chunks:
                    status, reply = NEARD.call("chunk", {"chunk_id": chunk["chunk_hash"]})
                    if status == 200:
                        self.chunks[chunk["chunk_hash"]] = reply["result"]
                        for tx in reply["result"]["transactions"]:
                            self.txs.append(dict(tx, height=height))
        self.accounts = sorted({t["signer_id"] for t in self.txs} | {t["receiver_id"] for t in self.txs} | {"node0", "node1"})
        self.final = NEARD.call("block", {"finality": "final"})[1]["result"]["header"]
        # a block that is final on both nodes, at which the state is compared
        self.at = self.blocks[self.final["height"] - 2] if (self.final["height"] - 2) in self.blocks else self.blocks[self.final["height"]]
        self.contracts = {}
        self.keys = {}
        for account in self.accounts:
            status, reply = NEARD.call("query", {"request_type": "view_account", "block_id": self.at["header"]["hash"], "account_id": account})
            if status == 200 and "result" in reply and "code_hash" in reply["result"]:
                if reply["result"]["code_hash"] != "1" * 32:
                    self.contracts[account] = reply["result"]["code_hash"]
            status, reply = NEARD.call("query", {"request_type": "view_access_key_list", "block_id": self.at["header"]["hash"], "account_id": account})
            if status == 200 and "result" in reply and "keys" in reply["result"]:
                self.keys[account] = [k["public_key"] for k in reply["result"]["keys"]]

    def heights_with(self, predicate, limit):
        found = []
        for height, block in sorted(self.blocks.items()):
            for chunk in block["chunks"]:
                view = self.chunks.get(chunk["chunk_hash"])
                if chunk["height_included"] == height and view and predicate(view):
                    found.append(height)
        return found[:limit]


def build_requests(chain: Chain) -> list[Request]:
    R: list[Request] = []
    add = lambda group, method, params, head=False, note="": R.append(Request(group, method, params, head, note))   # noqa: E731
    at = chain.at["header"]["hash"]
    at_height = chain.at["header"]["height"]
    # status, health, network_info
    add("status", "status", [], head=True)
    add("health", "health", [])
    add("network_info", "network_info", [])
    # gas_price
    add("gas_price", "gas_price", [None], head=True)
    add("gas_price", "gas_price", [at_height])
    add("gas_price", "gas_price", [at])
    add("gas_price", "gas_price", {"block_id": at_height})
    add("gas_price", "gas_price", [10 ** 9], note="unknown block")
    add("gas_price", "gas_price", ["11111111111111111111111111111111"], note="unknown block hash")
    # block
    for finality in ("final", "optimistic", "near-final"):
        add("block", "block", {"finality": finality}, head=True)
    add("block", "block", {"sync_checkpoint": "genesis"})
    add("block", "block", {"sync_checkpoint": "earliest_available"})
    heights = sorted({0, 1, 2, 3, 4, 5, 6, 7} | set(chain.heights_with(lambda c: c["transactions"], 12)) |
                     set(chain.heights_with(lambda c: c["receipts"], 12)) |
                     {h for h in chain.blocks if h % 30 in (0, 1, 29)} | {at_height})
    for h in heights:
        if h in chain.blocks:
            add("block", "block", {"block_id": h})
    for h in heights[:: max(1, len(heights) // 10)]:
        if h in chain.blocks:
            add("block", "block", {"block_id": chain.blocks[h]["header"]["hash"]})
    add("block", "block", [at_height], note="legacy form")
    add("block", "block", [at], note="legacy form")
    add("block", "block", {"block_id": 10 ** 9}, note="unknown block, above the head")
    add("block", "block", {"block_id": chain.head - 3}, note="a block that is there")
    add("block", "block", {"block_id": "11111111111111111111111111111111"}, note="unknown hash")
    add("block", "block", {"block_id": "abc"}, note="malformed hash")
    add("block", "block", {}, note="no reference")
    add("block", "block", None, note="no parameters")
    # chunk
    chunk_blocks = [h for h in heights if h in chain.blocks and chain.blocks[h]["chunks"]]
    for h in chunk_blocks[:30]:
        add("chunk", "chunk", {"block_id": h, "shard_id": 0})
    for chunk_hash in list(chain.chunks)[:: max(1, len(chain.chunks) // 25)]:
        add("chunk", "chunk", {"chunk_id": chunk_hash})
    some_chunk = next(iter(chain.chunks))
    add("chunk", "chunk", [some_chunk], note="legacy form")
    add("chunk", "chunk", [[at_height, 0]], note="legacy form")
    add("chunk", "chunk", {"block_id": at, "shard_id": 0})
    add("chunk", "chunk", {"chunk_id": "11111111111111111111111111111111"}, note="unknown chunk")
    add("chunk", "chunk", {"block_id": at_height, "shard_id": 7}, note="unknown shard")
    add("chunk", "chunk", {"block_id": 10 ** 9, "shard_id": 0}, note="unknown block")
    add("chunk", "chunk", {"shard_id": 0}, note="no block")
    # query: accounts, keys, code, state, call_function
    for account in chain.accounts:
        add("query/view_account", "query", {"request_type": "view_account", "block_id": at, "account_id": account})
    add("query/view_account", "query", {"request_type": "view_account", "block_id": at_height, "account_id": "node0"})
    add("query/view_account", "query", {"request_type": "view_account", "finality": "final", "account_id": "node0"}, head=True)
    add("query/view_account", "query", {"request_type": "view_account", "finality": "optimistic", "account_id": "ft.node0"}, head=True)
    add("query/view_account", "query", {"request_type": "view_account", "block_id": at, "account_id": "nosuch.node0"}, note="unknown account")
    add("query/view_account", "query", {"request_type": "view_account", "block_id": at, "account_id": "Not An Account"}, note="invalid account id")
    add("query/view_account", "query", {"request_type": "view_account", "block_id": 10 ** 9, "account_id": "node0"}, note="unknown block")
    add("query/view_account", "query", {"request_type": "view_account", "block_id": "11111111111111111111111111111111", "account_id": "node0"}, note="unknown block hash")
    add("query/view_account", "query", {"request_type": "view_account", "account_id": "node0"}, note="no block reference")
    add("query/view_account", "query", {"request_type": "view_foo", "finality": "final", "account_id": "node0"}, note="unknown request type")
    for account, keys in chain.keys.items():
        add("query/view_access_key_list", "query", {"request_type": "view_access_key_list", "block_id": at, "account_id": account})
        for key in keys[:3]:
            add("query/view_access_key", "query", {"request_type": "view_access_key", "block_id": at, "account_id": account, "public_key": key})
    add("query/view_access_key", "query", {"request_type": "view_access_key", "block_id": at, "account_id": "node0", "public_key": "ed25519:3j42zvap1bwqN5wEA2AL3PYdDdeRAs6NnVWcWA6cG13y"}, note="unknown key")
    add("query/view_access_key", "query", {"request_type": "view_access_key", "block_id": at, "account_id": "nosuch.node0", "public_key": "ed25519:3j42zvap1bwqN5wEA2AL3PYdDdeRAs6NnVWcWA6cG13y"}, note="unknown account")
    add("query/view_access_key_list", "query", {"request_type": "view_access_key_list", "block_id": at, "account_id": "nosuch.node0"}, note="unknown account")
    for account in chain.contracts:
        add("query/view_code", "query", {"request_type": "view_code", "block_id": at, "account_id": account})
        add("query/view_state", "query", {"request_type": "view_state", "block_id": at, "account_id": account, "prefix_base64": ""})
    add("query/view_code", "query", {"request_type": "view_code", "block_id": at, "account_id": "node0"}, note="no contract")
    add("query/view_code", "query", {"request_type": "view_code", "block_id": at, "account_id": "nosuch.node0"}, note="unknown account")
    add("query/view_state", "query", {"request_type": "view_state", "block_id": at, "account_id": "ft.node0", "prefix_base64": b64(b"\x00")})
    add("query/view_state", "query", {"request_type": "view_state", "block_id": at, "account_id": "ft.node0", "prefix_base64": "", "limit": 2})
    add("query/view_state", "query", {"request_type": "view_state", "block_id": at, "account_id": "nosuch.node0", "prefix_base64": ""}, note="unknown account")
    add("query/view_state", "query", {"request_type": "view_state", "block_id": at, "account_id": "ft.node0"}, note="no prefix")
    add("query/view_state", "query", {"request_type": "view_state", "block_id": at, "account_id": "ft.node0", "prefix_base64": "!!"}, note="not base64")
    if "ft.node0" in chain.contracts:
        add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "ft.node0", "method_name": "ft_total_supply", "args_base64": b64(b"{}")})
        add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "ft.node0", "method_name": "ft_metadata", "args_base64": b64(b"{}")})
        for account in ("node0", "a.node0", "ft.node0", "test1.node0"):
            add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "ft.node0", "method_name": "ft_balance_of", "args_base64": b64(json.dumps({"account_id": account}).encode())})
        add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "ft.node0", "method_name": "nosuch", "args_base64": b64(b"{}")}, note="no such method")
        add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "ft.node0", "method_name": "ft_balance_of", "args_base64": b64(b"not json")}, note="the contract panics")
    for account in ("test1.node0", "a.node0"):
        if account in chain.contracts:
            for method, args in (("sum_with_input", u64le(3) + u64le(4)), ("sum_n", u64le(2000)), ("fibonacci", bytes([15])),
                                 ("ext_account_id", b""), ("ext_account_balance", b""), ("ext_sha256", b"safe-near"),
                                 ("ext_signer_pk", b""), ("ext_predecessor_account_id", b""), ("read_value", u64le(0)),
                                 ("write_key_value", b"key-one" + u64le(1)), ("log_something", b"")):
                add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": account, "method_name": method, "args_base64": b64(args)})
    add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "node0", "method_name": "x", "args_base64": ""}, note="no contract")
    add("query/call_function", "query", {"request_type": "call_function", "block_id": at, "account_id": "nosuch.node0", "method_name": "x", "args_base64": ""}, note="unknown account")
    # transactions: every transaction of the chain
    for tx in chain.txs:
        add("tx", "tx", {"tx_hash": tx["hash"], "sender_account_id": tx["signer_id"], "wait_until": "FINAL"})
    for tx in chain.txs[:: max(1, len(chain.txs) // 30)]:
        add("EXPERIMENTAL_tx_status", "EXPERIMENTAL_tx_status", {"tx_hash": tx["hash"], "sender_account_id": tx["signer_id"], "wait_until": "FINAL"})
        add("tx", "tx", [tx["hash"], tx["signer_id"]], note="legacy form")
    add("tx", "tx", {"tx_hash": "11111111111111111111111111111111", "sender_account_id": "node0", "wait_until": "NONE"}, note="unknown transaction")
    add("tx", "tx", ["abc", "node0"], note="malformed hash")
    add("tx", "tx", {"sender_account_id": "node0"}, note="no hash")
    # state changes by kind of every block (EXPERIMENTAL_changes_in_block, which the Lean node keeps for its GC window)
    for h in sorted(chain.blocks):
        add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"block_id": h})
    for h in heights[:: max(1, len(heights) // 10)]:
        if h in chain.blocks:
            add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"block_id": chain.blocks[h]["header"]["hash"]})
    for finality in ("final", "optimistic", "near-final"):
        add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"finality": finality}, head=True)
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"sync_checkpoint": "genesis"})
    add("EXPERIMENTAL_changes_in_block", "block_effects", {"block_id": at_height}, note="the other name")
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"block_id": 10 ** 9}, note="unknown block, above the head")
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"block_id": "11111111111111111111111111111111"}, note="unknown hash")
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {"block_id": "abc"}, note="malformed hash")
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", {}, note="no reference")
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", [at_height], note="not a map")
    add("EXPERIMENTAL_changes_in_block", "EXPERIMENTAL_changes_in_block", None, note="no parameters")
    # EXPERIMENTAL_changes: the values, with their causes, of the keys each block touched, for every changes_type
    touched: dict[int, list[tuple[str, str]]] = {}
    for h in sorted(chain.blocks):
        status, reply = NEARD.call("EXPERIMENTAL_changes_in_block", {"block_id": h})
        if status == 200 and "result" in reply:
            touched[h] = [(c["type"], c["account_id"]) for c in reply["result"]["changes"]]
    group = "EXPERIMENTAL_changes"

    def accounts_of(h: int, kind: str) -> list[str]:
        return sorted({a for t, a in touched.get(h, []) if t == kind})
    for h in sorted(touched):
        by = {"account_touched": "account_changes", "contract_code_touched": "contract_code_changes",
              "access_key_touched": "all_access_key_changes"}
        for kind, changes_type in by.items():
            ids = accounts_of(h, kind)
            if ids:
                add(group, "EXPERIMENTAL_changes", {"block_id": h, "changes_type": changes_type, "account_ids": ids})
        ids = accounts_of(h, "data_touched")
        if ids:
            add(group, "EXPERIMENTAL_changes", {"block_id": h, "changes_type": "data_changes", "account_ids": ids, "key_prefix_base64": ""})
            add(group, "EXPERIMENTAL_changes", {"block_id": h, "changes_type": "data_changes", "account_ids": ids[:1], "key_prefix_base64": b64(b"key")},
                note="a prefix of the keys")
        ids = accounts_of(h, "access_key_touched")
        keys = [{"account_id": a, "public_key": k} for a in ids for k in chain.keys.get(a, [])[:3]]
        if keys:
            add(group, "EXPERIMENTAL_changes", {"block_id": h, "changes_type": "single_access_key_changes", "keys": keys})
    hash_heights = sorted(touched)[:: max(1, len(touched) // 12)]
    for h in hash_heights:
        ids = sorted({a for _, a in touched[h]})
        add(group, "EXPERIMENTAL_changes", {"block_id": chain.blocks[h]["header"]["hash"], "changes_type": "account_changes", "account_ids": ids},
            note="by hash, every account the block touched")
        add(group, "changes", {"block_id": h, "changes_type": "data_changes", "account_ids": ids, "key_prefix_base64": ""}, note="the other name")
    for finality in ("final", "optimistic", "near-final"):
        add(group, "EXPERIMENTAL_changes", {"finality": finality, "changes_type": "account_changes", "account_ids": chain.accounts}, head=True)
    add(group, "EXPERIMENTAL_changes", {"sync_checkpoint": "genesis", "changes_type": "account_changes", "account_ids": ["near", "node0"]})
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "account_changes", "account_ids": []}, note="no account")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "account_changes", "account_ids": ["nosuch.node0", "node0"]},
        note="an account that is not there")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "account_changes", "account_ids": ["node0", "node0"]},
        note="the same account twice")
    # the errors
    add(group, "EXPERIMENTAL_changes", {"block_id": 10 ** 9, "changes_type": "account_changes", "account_ids": ["node0"]}, note="unknown block")
    add(group, "EXPERIMENTAL_changes", {"block_id": "11111111111111111111111111111111", "changes_type": "account_changes", "account_ids": ["node0"]}, note="unknown hash")
    add(group, "EXPERIMENTAL_changes", {"block_id": "abc", "changes_type": "account_changes", "account_ids": ["node0"]}, note="malformed hash")
    add(group, "EXPERIMENTAL_changes", {"changes_type": "account_changes", "account_ids": ["node0"]}, note="no block reference")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height}, note="no changes_type")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "nosuch", "account_ids": []}, note="unknown changes_type")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": 5, "account_ids": []}, note="changes_type is not a string")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "account_changes"}, note="no account_ids")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "account_changes", "account_ids": "node0"}, note="account_ids is not a list")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "account_changes", "account_ids": ["Not Valid"]}, note="invalid account id")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "single_access_key_changes"}, note="no keys")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "single_access_key_changes", "keys": [{"account_id": "node0", "public_key": "bad"}]}, note="bad key")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "single_access_key_changes", "keys": [{"account_id": "node0", "public_key": "foo:xyz"}]}, note="unknown key type")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "data_changes", "account_ids": ["node0"]}, note="no key_prefix_base64")
    add(group, "EXPERIMENTAL_changes", {"block_id": at_height, "changes_type": "data_changes", "account_ids": ["node0"], "key_prefix_base64": "!!"}, note="not base64")
    add(group, "EXPERIMENTAL_changes", {}, note="no parameters")
    add(group, "EXPERIMENTAL_changes", [at_height], note="not a map")
    add(group, "EXPERIMENTAL_changes", None, note="null")
    # validators and configuration
    add("validators", "validators", [None], head=True)
    add("validators", "validators", {"epoch_id": chain.at["header"]["epoch_id"]}, note="an epoch that is over or the current one")
    add("validators", "validators", {"epoch_id": "11111111111111111111111111111111"}, note="unknown epoch")
    add("validators", "validators", [10 ** 9], note="a block that is not there")
    add("EXPERIMENTAL_protocol_config", "EXPERIMENTAL_protocol_config", {"finality": "final"})
    add("EXPERIMENTAL_protocol_config", "EXPERIMENTAL_protocol_config", {"block_id": at})
    add("EXPERIMENTAL_protocol_config", "EXPERIMENTAL_protocol_config", {"block_id": 10 ** 9}, note="unknown block")
    add("EXPERIMENTAL_genesis_config", "EXPERIMENTAL_genesis_config", {})
    add("EXPERIMENTAL_genesis_config", "EXPERIMENTAL_genesis_config", [])
    add("EXPERIMENTAL_genesis_config", "genesis_config", [])
    # protocol errors
    add("errors", "nosuchmethod", [], note="unknown method")
    add("errors", "block", [1, 2, 3], note="too many parameters")
    return R


def exercise(requests: list[Request], verbose: bool = True) -> list[dict]:
    results = []
    for request in requests:
        result = compare(request)
        results.append(result)
        if verbose and not result["equal"]:
            print(f"DIFF {request.group} {request.method} {json.dumps(request.params)[:140]} {request.note}")
            for line in result["diff"][:6]:
                print("     ", line)
    return results


def summary(results: list[dict]) -> dict:
    table: dict[str, dict] = {}
    for result in results:
        group = result["request"].group
        row = table.setdefault(group, {"requests": 0, "equal": 0, "errors": 0, "stale": 0, "unrendered_failures": 0})
        row["unrendered_failures"] += result.get("unrendered", 0)
        row["requests"] += 1
        row["equal"] += 1 if result["equal"] else 0
        row["errors"] += 1 if result.get("ok") is False else 0
        row["stale"] += 1 if result.get("stale") else 0
    return table


# --------------------------------------------------------------------------------------------------------------------
# transactions through the Lean RPC, and the restart

def find_signer(chain: Chain):
    """An account of the workload whose key is derivable: ``(account, key)``."""
    for account in chain.accounts:
        key = nc.Key.derive(f"{SEED}/{account}")
        if key.text in chain.keys.get(account, []):
            return account, key
    raise SystemExit("no account of the workload has a derivable key")


def nonce_of(account: str, key) -> int:
    reply = NEARD.call("query", {"request_type": "view_access_key", "finality": "final", "account_id": account,
                                 "public_key": key.text})[1]
    return reply["result"]["nonce"]


def tx_phase(chain: Chain) -> list[dict]:
    """Sends transactions to the Lean node (valid ones, then invalid ones to both nodes); the valid ones must land on
    the chain: both nodes then answer ``tx`` alike."""
    account, key = find_signer(chain)
    receiver = "node0"
    block_hash = nc.b58decode(NEARD.call("block", {"finality": "final"})[1]["result"]["header"]["hash"])
    nonce = nonce_of(account, key)
    results: list[dict] = []
    sent: list[tuple[str, str]] = []

    def signed(n, to=receiver, deposit=1, signer=account, k=key, hash_=block_hash):
        return nc.transaction(signer, k, n, to, hash_, [nc.transfer(deposit)])

    def b64s(raw): return base64.b64encode(raw).decode()

    # the valid ones, through the Lean node only
    plan = [("send_tx", {"signed_tx_base64": b64s(signed(nonce + 1)), "wait_until": "FINAL"}, nonce + 1),
            ("broadcast_tx_async", [b64s(signed(nonce + 2))], nonce + 2),
            ("broadcast_tx_commit", [b64s(signed(nonce + 3))], nonce + 3)]
    for method, params, n in plan:
        status, reply = LEAN.call(method, params, timeout=90)
        raw = signed(n)
        h = nc.b58encode(nc.transaction_hash(raw))
        ok = status == 200 and "result" in reply
        results.append({"request": Request("lean_rpc_tx/" + method, method, params, note=f"nonce {n}"), "equal": ok,
                        "diff": [] if ok else [json.dumps(reply)[:300]], "ok": ok})
        sent.append((h, account))
    # they land: the final status on both nodes is the same
    for h, signer in sent:
        request = Request("lean_rpc_tx/landed", "tx", {"tx_hash": h, "sender_account_id": signer, "wait_until": "FINAL"}, head=False)
        deadline = time.time() + 120
        result = compare(request)
        while time.time() < deadline and (not result["equal"] or not result["ok"]):
            time.sleep(2)
            result = compare(request)
        results.append(result)
    # the invalid ones, to both nodes: same error
    junk = bytearray(signed(nonce + 10)); junk[-1] ^= 1
    expired = nc.b58decode(chain.blocks[1]["header"]["hash"]) if 1 in chain.blocks else block_hash
    other = nc.Key.derive("not-a-key-of-anyone")
    cases = {
        "bad nonce": signed(1),
        "unknown signer": signed(nonce + 11, signer="nobody-here.node0"),
        "wrong key": signed(nonce + 12, k=other),
        "insufficient balance": signed(nonce + 13, deposit=10 ** 33),
        "bad signature": bytes(junk),
        "expired": signed(nonce + 14, hash_=expired),
        "unknown receiver": signed(nonce + 15, to="nobody-here.node0"),
        "malformed": b"\x00\x01\x02",
    }
    for name, raw in cases.items():
        for method, params in (("send_tx", {"signed_tx_base64": b64s(raw), "wait_until": "NONE"}),
                               ("broadcast_tx_async", [b64s(raw)])):
            results.append(compare(Request("tx_errors/" + method, method, params, note=name)))
    return results


def finals() -> tuple:
    return (NEARD.call("block", {"finality": "final"})[1]["result"]["header"]["height"],
            LEAN.call("block", {"finality": "final"})[1]["result"]["header"]["height"])


def restart_phase(chain: Chain, work: Path, binary: Path, home: Path, old: subprocess.Popen) -> tuple[dict, list[dict]]:
    """Kills the Lean validator, starts it again from its store; finality must go on and the responses stay equal."""
    before = finals()
    os.killpg(old.pid, signal.SIGKILL)
    old.wait()
    killed_at = time.time()
    time.sleep(8)
    stalled = NEARD.call("block", {"finality": "final"})[1]["result"]["header"]["height"]
    lean = va.start_lean(home, work, 24 * 3600, binary, lean_extra(home), log_name="lean-restart.log")
    wait_for(lambda: LEAN.call("status", [])[1]["result"]["sync_info"]["latest_block_height"] >= before[0], 180,
             "the Lean node did not come back")
    resumed_in = time.time() - killed_at
    wait_for(lambda: finals()[0] >= stalled + 8 and finals()[1] >= stalled + 8, 240, "finality did not continue")
    after = finals()
    report = {"final_before_kill": before[0], "final_while_down": stalled, "final_after_restart": after,
              "seconds_to_catch_up": round(resumed_in, 1), "process": lean.pid}
    requests = [Request("after_restart/status", "status", [], head=True),
                Request("after_restart/block", "block", {"finality": "final"}, head=True),
                Request("after_restart/block", "block", {"block_id": chain.final["height"]}),
                Request("after_restart/validators", "validators", [None], head=True),
                Request("after_restart/gas_price", "gas_price", [None], head=True)]
    return report | {"_lean": lean}, exercise(requests)


def run(options) -> int:
    home, lean, load = bring_up(options.work, options.binary, True)
    code = 1
    try:
        wait_for(lambda: load.poll() is not None, 3600, "the workload did not end", step=5)
        time.sleep(15)
        chain = Chain()
        requests = build_requests(chain)
        print(len(requests), "requests", flush=True)
        results = exercise(requests)
        txs = tx_phase(chain)
        for r in txs:
            if not r["equal"]:
                print("DIFF", r["request"].group, r["request"].method, r["request"].note, r["diff"][:4])
        results += txs
        restart, after = restart_phase(chain, options.work, options.binary, home, lean)
        lean = restart.pop("_lean")
        results += after
        table = summary(results)
        for group, row in sorted(table.items()):
            print(f"{group:32} {row}")
        print("restart:", restart)
        print("unrendered failures at the Lean node (neard's payload):", dict(UNRENDERED_KINDS))
        total = len(results)
        equal = sum(1 for r in results if r["equal"])
        print(f"{equal}/{total} requests equal, 0 known gaps, {total - equal} other differences")
        (options.work / "rpc-conformance.json").write_text(json.dumps(
            {"table": table, "restart": restart, "requests": total, "equal": equal,
             "diffs": [{"group": r["request"].group, "method": r["request"].method, "note": r["request"].note,
                        "diff": r["diff"][:6]} for r in results if not r["equal"]],
             "normalisation": NORMALISATION}, indent=1))
        code = 0 if equal == total else 1
    finally:
        for process in (load, lean):
            if process and process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        localnet.stop(TOPOLOGY)
    return code


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
    parser.add_argument("mode", choices=["serve", "run", "check"], nargs="?", default="run")
    parser.add_argument("--binary", type=Path, default=va.BINARY)
    parser.add_argument("--work", type=Path, default=localnet.DATA / "rpc-run")
    parser.add_argument("--no-workload", action="store_true")
    parser.add_argument("--gc-epochs", type=int, default=None, help="--gc-epochs-to-keep of the Lean node (default: its own)")
    options = parser.parse_args()
    if options.gc_epochs is not None:
        GC_EPOCHS[:] = [options.gc_epochs]
    options.work.mkdir(parents=True, exist_ok=True)
    (options.work / "serve-stop").unlink(missing_ok=True)
    if options.mode == "serve":
        serve(options)
    elif options.mode == "check":
        chain = Chain()
        requests = build_requests(chain)
        print(len(requests), "requests", flush=True)
        results = exercise(requests)
        for group, row in sorted(summary(results).items()):
            print(f"{group:32} {row}")
        sys.exit(0 if all(r["equal"] for r in results) else 1)
    else:
        sys.exit(run(options))


if __name__ == "__main__":
    main()
