#!/usr/bin/env python3
"""Acceptance of the validator (M8): `just localnet-validator`.

A two-validator, one-shard localnet whose second validator is the Lean node.  Both hold half of the stake
(``localnet.TOPOLOGIES["validator"]``), so neither can finalize alone: every approval, chunk endorsement and
block the Lean node contributes is needed.  The run

1. initializes the topology and lets ``neard`` (node0) write the genesis of the chain, then exports the genesis
   block and the files the Lean node starts from (``prepare``);
2. starts ``neard`` and ``near-lean-node validator`` (from node1's keys), with the workload on ``neard``'s RPC;
3. watches both for ``--duration`` seconds, then stops them and checks (``analyse``): both made progress; blocks
   and chunks produced by the Lean node were accepted by ``neard`` (they are on its chain, with the Lean node
   as producer); the state root of every block agrees over RPC; the final head advanced; no disconnect.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import urllib.error

import chain_apply
import chain_corpus
import localnet
import nearcodec as nc

ROOT = chain_corpus.ROOT
TOPOLOGY = "validator"
BINARY = ROOT / "near-lean/node/.lake/build/bin/near-lean-node"
CORPUS_META = chain_corpus.DEFAULT_CORPUS / "single/meta.json"


def rpc(method: str, params, index: int = 0, timeout: float = 10):
    reply = localnet.rpc(TOPOLOGY, method, params, index=index, timeout=timeout)
    if "error" in reply:
        raise RuntimeError(json.dumps(reply["error"])[:300])
    return reply["result"]


def wait_for(predicate, timeout: float, what: str):
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            value = predicate()
            if value:
                return value
        except Exception:
            pass
        time.sleep(0.5)
    raise TimeoutError(what)


def prepare(work: Path) -> Path:
    """Initialize the topology; write the files the Lean node starts from into ``work``."""
    localnet.stop(TOPOLOGY)
    home = localnet.init(TOPOLOGY)
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True, exist_ok=True)
    localnet.start(TOPOLOGY)          # node0 alone: it writes the genesis, then waits for its second validator
    genesis_hash = wait_for(lambda: rpc("status", [])["genesis_hash"], 60, "neard did not start")
    time.sleep(2)
    localnet.stop(TOPOLOGY)
    out = home / "chain"
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir()
    node = home / "node0"
    copy = home / "export-copy"
    shutil.rmtree(copy, ignore_errors=True)
    shutil.copytree(node, copy)
    # the exporter writes the genesis block and the epochs first; its variants need a block to vary, which a
    # chain of the genesis alone does not have, so it stops there (a rebuilt exporter does not)
    subprocess.run([str(chain_corpus.EXPORTER), "--home", str(copy), "--out", str(out), "--writable", "--bases", "0",
                    "--seed", "1", "--key", str(node / "validator_key.json"),
                    "--key", str(home / "node1/validator_key.json")], capture_output=True)
    shutil.rmtree(copy, ignore_errors=True)
    blocks = (out / "blocks.jsonl").read_text().splitlines()
    if len(blocks) != 1:
        raise SystemExit(f"the exporter wrote {len(blocks)} blocks, expected the genesis alone")
    genesis_block = json.loads(blocks[0])
    if nc.b58decode(genesis_hash).hex() != genesis_block["hash"]:
        raise SystemExit("the exported genesis block is not neard's")
    g = json.loads((node / "genesis.json").read_text())
    single = json.loads(CORPUS_META.read_text())
    meta = {
        "formatVersion": 1, "chainId": g["chain_id"], "protocolVersion": g["protocol_version"],
        "genesisHeight": g["genesis_height"], "genesisHash": genesis_block["hash"], "headHeight": 0, "blocks": 1,
        "epochLength": g["epoch_length"], "shardLayoutStatic": True, "minGasPrice": g["min_gas_price"],
        "maxGasPrice": g["max_gas_price"], "gasPriceAdjustmentRateNumer": g["gas_price_adjustment_rate"][0],
        "gasPriceAdjustmentRateDenom": g["gas_price_adjustment_rate"][1], "gasLimit": g["gas_limit"],
        "totalSupply": g["total_supply"], "transactionValidityPeriod": g["transaction_validity_period"],
        "variants": 0, "variantKinds": [], "baseHeights": [], "epochs": 1,
        # the BlockInfo of the zero hash is the same on every localnet of the pinned release
        "zeroHashBlockInfo": single["zeroHashBlockInfo"],
    }
    (work / "meta.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
    (work / "genesis.json").write_text(json.dumps(chain_apply.genesis_file(TOPOLOGY), indent=1, sort_keys=True) + "\n")
    (work / "blocks.jsonl").write_text(blocks[0] + "\n")
    return home


def start_lean(home: Path, work: Path, seconds: int, binary: Path, extra: list[str] | None = None,
               log_name: str = "lean.log") -> subprocess.Popen:
    boot_key = json.loads((home / "node0/node_key.json").read_text())["public_key"]
    port = localnet.network_port(TOPOLOGY, 0)
    command = [str(binary), "validator", "--chain-dir", str(work),
               "--node-key", str(home / "node1/node_key.json"), "--validator-key", str(home / "node1/validator_key.json"),
               "--boot", f"{boot_key}@127.0.0.1:{port}", "--listen", str(localnet.network_port(TOPOLOGY, 1)),
               "--seconds", str(seconds), "--report", str(work / "report.json"),
               "--applied-log", str(work / "applied.jsonl"), "--stop-file", str(work / "stop"), "--configs", str(ROOT / "near-lean/vm/configs")]
    command += extra or []
    log = (work / log_name).open("a" if log_name != "lean.log" else "w")
    return subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, cwd=ROOT, start_new_session=True)


def start_workload(work: Path, steady: int) -> subprocess.Popen:
    command = [sys.executable, str(Path(__file__).with_name("workload.py")), TOPOLOGY, "--skip", "hostcalls", "burst", "wait"]
    if steady:
        command += ["--steady", str(steady)]
    return subprocess.Popen(command, stdout=(work / "workload.log").open("w"), stderr=subprocess.STDOUT,
                            cwd=Path(__file__).parent)


def head_height() -> int:
    return rpc("status", [])["sync_info"]["latest_block_height"]


def final_height() -> int:
    return rpc("block", {"finality": "final"})["header"]["height"]


def stall_test(lean: subprocess.Popen, seconds: int = 12) -> dict:
    """Stops the Lean node: the chain must stop with it (its stake is more than a third), and go on when it does."""
    before, final_before = head_height(), final_height()
    os.killpg(lean.pid, signal.SIGSTOP)
    time.sleep(seconds)
    during, final_during = head_height(), final_height()
    os.killpg(lean.pid, signal.SIGCONT)
    time.sleep(seconds)
    after, final_after = head_height(), final_height()
    return {"seconds": seconds, "headBefore": before, "headWhileStopped": during, "headAfter": after,
            "finalBefore": final_before, "finalWhileStopped": final_during, "finalAfter": final_after,
            "stalled": during - before <= 2, "resumed": after - during >= 5}


def neard_holds(hash_hex: str) -> bool:
    """Whether neard holds the block (on its canonical chain or not)."""
    try:
        rpc("block", {"block_id": nc.b58encode(bytes.fromhex(hash_hex))})
        return True
    except (RuntimeError, urllib.error.HTTPError):
        return False


def chain_rows(last: int) -> list[dict]:
    """Every block of neard's chain with its producer and its chunks."""
    rows = []
    for height in range(1, last + 1):
        try:
            block = rpc("block", {"block_id": height})
        except (RuntimeError, urllib.error.HTTPError):
            continue                    # a skipped height
        header = block["header"]
        chunks = []
        for chunk in block["chunks"]:
            detail = rpc("chunk", {"chunk_id": chunk["chunk_hash"]})
            chunks.append({"shard": chunk["shard_id"], "new": chunk["height_included"] == height,
                           "author": detail["author"], "prevStateRoot": chunk["prev_state_root"],
                           "hash": chunk["chunk_hash"],
                           "txs": [(t["hash"], t["signer_id"]) for t in detail.get("transactions", [])]
                           if chunk["height_included"] == height else []})
        rows.append({"height": height, "hash": header["hash"], "author": block["author"], "chunks": chunks,
                     "approvals": sum(1 for a in header["approvals"] if a), "lastFinal": header["last_final_block"]})
    return rows


def neard_status_text(status) -> str:
    """The status of an outcome as the Lean node's applied log writes it."""
    if isinstance(status, dict):
        if "SuccessValue" in status:
            return "value:" + base64.b64decode(status["SuccessValue"]).hex()
        if "SuccessReceiptId" in status:
            return "receipt:" + nc.b58decode(status["SuccessReceiptId"]).hex()
        if "Failure" in status:
            return "failure"
    return "unknown"


def outcome_comparison(applied: list[dict], rows: list[dict]) -> dict:
    """Every transaction of a chunk the Lean node produced (and a sample of neard's): the outcomes of the
    transaction and of its receipts, from neard's ``EXPERIMENTAL_tx_status``, against those the Lean node
    computed when it applied the blocks."""
    lean_outcomes = {}
    for row in applied:
        for chunk in row["chunks"]:
            for o in chunk.get("outcomes", []):
                lean_outcomes[o["id"]] = o
    wanted = []
    for r in rows:
        for c in r["chunks"]:
            for tx_hash, signer in c["txs"]:
                wanted.append((c["author"] == "node1", tx_hash, signer, r["height"]))
    checked = equal = 0
    problems = []
    by_lean = [w for w in wanted if w[0]]
    by_neard = [w for w in wanted if not w[0]]
    for lean_made, tx_hash, signer, height in by_lean + by_neard[:40]:
        try:
            status = rpc("EXPERIMENTAL_tx_status", {"tx_hash": tx_hash, "sender_account_id": signer,
                                                    "wait_until": "FINAL"}, timeout=30)
        except Exception as error:      # noqa: BLE001
            problems.append(f"{tx_hash}: {error}")
            continue
        theirs = [status["transaction_outcome"]] + status.get("receipts_outcome", [])
        for o in theirs:
            checked += 1
            oid = nc.b58decode(o["id"]).hex()
            mine = lean_outcomes.get(oid)
            if mine is None:
                problems.append(f"height {height} {o['id']}: no outcome in the Lean node's log")
                continue
            out = o["outcome"]
            want = {"gasBurnt": out["gas_burnt"], "tokensBurnt": out["tokens_burnt"], "executor": out["executor_id"],
                    "status": neard_status_text(out["status"]),
                    "receipts": [nc.b58decode(r).hex() for r in out["receipt_ids"]]}
            have = {k: mine[k] for k in want}
            if want == have:
                equal += 1
            else:
                problems.append(f"height {height} {o['id']}: neard {want} Lean {have}")
    return {"leanTransactions": len(by_lean), "neardTransactionsChecked": min(len(by_neard), 40),
            "outcomesChecked": checked, "outcomesEqual": equal, "problems": problems[:10]}


def analyse(work: Path, report: dict, stall: dict | None, rows: list[dict], head: int, final: int,
            require_txs: bool = True, known=None) -> dict:
    """``known(hash_hex)`` tells whether neard holds the block with that hash (also off its canonical chain).  After a pause
    both producers can build on the same parent at different heights (nearcore does it too: a block per height whose
    approvals are ready), and the fork choice orphans some blocks.  What is guaranteed is that every block the Lean node
    applied is valid for neard, i.e. neard accepted and stored it; a block off neard's chain is an orphan if neard holds it."""
    applied = [json.loads(line) for line in (work / "applied.jsonl").read_text().splitlines() if line.strip()]
    by_height = {r["height"]: r for r in rows}
    result: dict = {"headHeight": head, "finalHeight": final}
    lean = "node1"
    result["blocksByLean"] = sum(1 for r in rows if r["author"] == lean)
    result["blocksByNeard"] = sum(1 for r in rows if r["author"] != lean)
    result["chunksByLean"] = sum(1 for r in rows for c in r["chunks"] if c["new"] and c["author"] == lean)
    result["chunksByNeard"] = sum(1 for r in rows for c in r["chunks"] if c["new"] and c["author"] != lean)
    # the Lean node's chain is neard's chain, block by block, with the same state roots
    same_hash = same_root = checked_root = 0
    problems = []
    orphans = []
    lean_hashes = {}
    for row in applied:
        mine = by_height.get(row["height"])
        if mine is None or nc.b58decode(mine["hash"]).hex() != row["hash"]:
            if known is not None and known(row["hash"]):
                orphans.append(row["height"])
            elif mine is None:
                problems.append(f"height {row['height']}: not in neard's chain, and neard does not hold the block")
            else:
                problems.append(f"height {row['height']}: block hash differs, and neard does not hold the block")
            continue
        lean_hashes[row["height"]] = row["hash"]
        same_hash += 1
        nxt = by_height.get(row["height"] + 1)
        if nxt:
            for chunk, report_chunk in zip(nxt["chunks"], row["chunks"]):
                if chunk["new"]:
                    checked_root += 1
                    if nc.b58decode(chunk["prevStateRoot"]).hex() == report_chunk["stateRoot"]:
                        same_root += 1
                    else:
                        problems.append(f"height {row['height']} shard {chunk['shard']}: state root differs")
    result.update(blocksApplied=len(applied), sameHash=same_hash, orphans=orphans, stateRootsChecked=checked_root, stateRootsEqual=same_root,
                  problems=problems[:10], disconnects=[d for d in report.get("disconnects", []) if "connection refused" not in d], failure=report.get("failure"),
                  leanStats=report.get("stats", {}), stall=stall)
    lean_tx_chunks = [(r["height"], c) for r in rows for c in r["chunks"]
                      if c["new"] and c["author"] == lean and c["txs"]]
    result["leanChunksWithTransactions"] = len(lean_tx_chunks)
    result["leanTransactionsIncluded"] = sum(len(c["txs"]) for _, c in lean_tx_chunks)
    result["outcomes"] = outcome_comparison(applied, rows)
    # neard's blocks signed by the Lean node verify on neard's side by being in its chain; finality moved
    result["finalityAdvanced"] = final > 5 and head - final < 20
    ok = (result["blocksByLean"] > 0 and result["chunksByLean"] > 0 and not problems and not result["failure"]
          and not result["disconnects"] and report.get("handshakes") == 1 and same_hash + len(orphans) == len(applied) and same_root == checked_root and checked_root > 0
          and result["finalityAdvanced"]
          and (not require_txs or (result["leanChunksWithTransactions"] > 0
                                   and result["outcomes"]["outcomesChecked"] > 0
                                   and result["outcomes"]["outcomesChecked"] == result["outcomes"]["outcomesEqual"]))
          and (stall is None or (stall["stalled"] and stall["resumed"])))
    result["ok"] = ok
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--duration", type=int, default=240, help="seconds to run")
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("--work", type=Path, default=localnet.DATA / "validator-run")
    parser.add_argument("--no-workload", action="store_true")
    parser.add_argument("--no-stall", action="store_true")
    options = parser.parse_args()
    home = prepare(options.work)
    localnet.start(TOPOLOGY)
    lean = start_lean(home, options.work, options.duration + 120, options.binary)
    workload = None
    stall = None
    try:
        wait_for(lambda: head_height() >= 3, 120, "the chain did not start")
        if not options.no_workload:
            workload = start_workload(options.work, options.duration)
        time.sleep(max(0, options.duration - (0 if options.no_stall else 30)))
        if not options.no_stall:
            stall = stall_test(lean)
        head, final = head_height(), final_height()
        (options.work / "stop").write_text("stop")
        lean.wait(timeout=60)
        rows = chain_rows(head_height())   # the chain went on while the Lean node was stopping
        report = json.loads((options.work / "report.json").read_text()) if (options.work / "report.json").exists() else {}
        result = analyse(options.work, report, stall, rows, head, final, require_txs=not options.no_workload, known=neard_holds)
        print(json.dumps(result, indent=1))
        (options.work / "result.json").write_text(json.dumps(result, indent=1) + "\n")
        sys.exit(0 if result["ok"] else 1)
    finally:
        if workload and workload.poll() is None:
            workload.kill()
        try:
            os.killpg(lean.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        localnet.stop(TOPOLOGY)


if __name__ == "__main__":
    main()
