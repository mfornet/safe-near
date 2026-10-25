#!/usr/bin/env python3
"""Acceptance of the peer protocol (M6): the Lean node as a peer of the pinned `neard` localnet.

``just localnet-peer`` runs this.  It starts the localnet of a topology, the workload (without its heavy
scenarios, which the Lean interpreter needs minutes for), and ``near-lean-node peer`` as a non-validator peer
with the boot node's address and key.  The node validates every block from the genesis to the head and keeps
following; its applied chunks are compared with the chain.  Checks, in order:

* the handshake completes on both sides: the node reports it and `neard`'s ``network_info`` lists the node's
  peer id among its active peers;
* the node's routing table exchange: it received and verified the edge(s) of `neard`'s table;
* every block up to `neard`'s head (at the time the node reached it) validated, and the node followed new
  blocks for ``--follow`` seconds without disconnecting;
* for every block the node applied, the state root of each shard equals ``prev_state_root`` of the chunk in the
  next block, as `neard` returns it over RPC, and the node's own comparison of the whole ChunkExtra and of the
  outgoing receipts with the next chunk's header and body found no difference.

The node starts from the genesis files of the M5 block corpus of the same topology (the genesis block with the
`BlockInfo` nearcore derived from it); the localnet's genesis is deterministic and its hash is checked here.
"""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time

import chain_apply
import chain_corpus
import localnet
import nearcodec as nc

ROOT = chain_corpus.ROOT
BINARY = ROOT / "near-lean/node/.lake/build/bin/near-lean-node"
HEAVY = ["hostcalls", "burst", "wait"]


def bootstrap(topology: str, directory: Path, genesis_hash: str) -> None:
    """The files the node starts from: configuration, genesis, and the genesis block of the corpus."""
    corpus = chain_corpus.DEFAULT_CORPUS / topology
    meta = json.loads((corpus / "meta.json").read_text())
    if meta["genesisHash"] != nc.b58decode(genesis_hash).hex():
        raise SystemExit(f"the localnet's genesis {genesis_hash} is not the one of the corpus {meta['genesisHash']}")
    (directory / "meta.json").write_bytes((corpus / "meta.json").read_bytes())
    genesis = chain_apply.genesis_file(topology)
    (directory / "genesis.json").write_text(json.dumps(genesis, indent=1, sort_keys=True) + "\n")
    with gzip.open(corpus / "blocks.jsonl.gz", "rt") as blocks:
        (directory / "blocks.jsonl").write_text(blocks.readline())


def run_workload(topology: str, skip: list[str], log: Path) -> subprocess.Popen:
    return subprocess.Popen([sys.executable, str(Path(__file__).with_name("workload.py")), topology, "--skip"] + skip,
                            stdout=log.open("w"), stderr=subprocess.STDOUT, cwd=Path(__file__).parent)


def rpc(topology: str, method: str, params):
    reply = localnet.rpc(topology, method, params)
    if "error" in reply:
        raise RuntimeError(json.dumps(reply["error"])[:200])
    return reply["result"]


def compare_roots(topology: str, applied: Path) -> tuple[int, int, list[str]]:
    """Each applied block's shard state roots against the next block's chunk headers, over RPC."""
    rows = [json.loads(line) for line in applied.read_text().splitlines() if line.strip()]
    checked = agree = 0
    problems = []
    for row in rows:
        height = row["height"]
        for chunk in row["chunks"]:
            shard = chunk["shard"]
            try:
                header = rpc(topology, "chunk", {"block_id": height + 1, "shard_id": shard})["header"]
            except RuntimeError:
                continue            # the last block applied: its child is not known to the chain yet
            if header["height_included"] != height + 1:
                continue            # no new chunk in the next block
            checked += 1
            if nc.b58decode(header["prev_state_root"]).hex() == chunk["stateRoot"]:
                agree += 1
            else:
                problems.append(f"block {height} shard {shard}: state root differs from the next chunk's")
    return checked, agree, problems


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--topologies", nargs="*", default=["single"], choices=sorted(localnet.TOPOLOGIES))
    parser.add_argument("--follow", type=int, default=300, help="seconds to keep following after reaching the head")
    parser.add_argument("--limit", type=int, default=3600, help="seconds before the run is cut")
    parser.add_argument("--drain", type=int, default=600, help="seconds to let the node apply what it validated")
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("--full-workload", action="store_true", help="include the heavy scenarios")
    options = parser.parse_args()
    ok = True
    for topology in options.topologies:
        ok = accept(topology, options) and ok
    print("localnet-peer: " + ("all agree" if ok else "FAILED"))
    sys.exit(0 if ok else 1)


def accept(topology: str, options: argparse.Namespace) -> bool:
    localnet.stop(topology)
    localnet.init(topology)
    localnet.start(topology)
    node_dir = localnet.home(topology) / "node0"
    boot_key = json.loads((node_dir / "node_key.json").read_text())["public_key"]
    port = localnet.network_port(topology, 0)
    result = False
    workload = None
    try:
        localnet.wait_ready(topology)
        genesis_hash = rpc(topology, "status", [])["genesis_hash"]
        with tempfile.TemporaryDirectory(prefix="safe-near-peer-") as temporary:
            work = Path(temporary)
            bootstrap(topology, work, genesis_hash)
            skip = [] if options.full_workload else HEAVY
            workload = run_workload(topology, skip, work / "workload.log")
            report = work / "report.json"
            applied = work / "applied.jsonl"
            command = [str(options.binary), "peer", "--chain-dir", str(work), "--node-key", str(work / "node_key.json"),
                       "--boot", f"{boot_key}@127.0.0.1:{port}", "--listen", str(port + 100),
                       "--store", str(work / "store"), "--follow", str(options.follow),
                       "--drain", str(options.drain), "--seconds", str(options.limit),
                       "--applied-log", str(applied), "--report", str(report),
                       "--configs", str(ROOT / "near-lean/vm/configs")]
            node = subprocess.Popen(command, stdout=subprocess.DEVNULL, stderr=(work / "node.log").open("w"))
            listed = False
            started = time.time()
            while node.poll() is None:
                try:
                    key_file = work / "node_key.json"
                    if key_file.exists():
                        node_id = json.loads(key_file.read_text())["public_key"]
                        listed = listed or any(p["id"] == node_id for p in rpc(topology, "network_info", [])["active_peers"])
                except Exception:
                    pass
                time.sleep(3)
                if time.time() - started > options.limit + 600:
                    node.kill()
            summary = json.loads(report.read_text()) if report.exists() else {}
            print((work / "node.log").read_text()[-3000:])
            peers = rpc(topology, "network_info", [])
            checked, agree, problems = compare_roots(topology, applied) if applied.exists() else (0, 0, ["no log"])
            head = rpc(topology, "status", [])["sync_info"]["latest_block_height"]
            tip = summary.get("tipHeight", 0)
            applied_height = summary.get("appliedHeight", 0)
            print(json.dumps({k: summary.get(k) for k in (
                "handshakes", "disconnects", "blocksValidated", "tipHeight", "peerHeight", "appliedHeight",
                "blocksApplied", "chunksApplied", "extrasChecked", "extrasAgree", "receiptsChecked",
                "receiptsAgree", "edgesVerified", "edgesInvalid", "reachedHeadAtSeconds", "seconds", "failure")}))
            checks = {
                "handshake completed on the node": summary.get("handshakes", 0) >= 1,
                "neard lists the node among its active peers": listed,
                "no disconnect": not summary.get("disconnects"),
                "routing table edges verified": summary.get("edgesVerified", 0) >= 1 and summary.get("edgesInvalid", 1) == 0,
                "reached neard's head": summary.get("reachedHeadAtSeconds") is not None,
                "no failure": summary.get("failure") is None and not summary.get("mismatches"),
                "ChunkExtra equal to the next chunk header's": summary.get("extrasChecked", 0) > 0
                    and summary.get("extrasChecked") == summary.get("extrasAgree"),
                "outgoing receipts equal to the next chunk body's": summary.get("receiptsChecked") == summary.get("receiptsAgree"),
                "state roots equal over RPC": checked > 0 and checked == agree,
            }
            for name, good in checks.items():
                print(f"  {'ok  ' if good else 'FAIL'} {name}")
            for p in problems[:10] + summary.get("mismatches", [])[:10]:
                print("  " + p)
            lag = head - applied_height
            print(f"{topology}: validated {summary.get('blocksValidated')} blocks up to {tip} (neard at {head}), applied "
                  f"{summary.get('blocksApplied')} blocks ({summary.get('chunksApplied')} chunks) up to {applied_height}, "
                  f"lag {lag} blocks, {checked} state roots compared over RPC, {agree} equal; "
                  f"{len(summary.get('disconnects', []))} disconnects; followed {summary.get('seconds')} s")
            result = all(checks.values())
    finally:
        if workload is not None and workload.poll() is None:
            workload.kill()
        localnet.stop(topology)
    return result


if __name__ == "__main__":
    main()
