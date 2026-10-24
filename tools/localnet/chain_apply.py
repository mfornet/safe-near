#!/usr/bin/env python3
"""Inputs of the Lean chain apply (M5b) that the block corpus does not carry, and the runner.

``extras`` adds two files to each topology of ``near-lean/node/corpus/blocks`` and to its manifest:

* ``genesis.json``: the genesis configuration the Lean node starts from (validators, economics,
  shard layout as Borsh, account and access key records with hex-encoded keys), taken from the
  localnet's ``genesis.json`` without interpretation;
* ``chunks.jsonl.gz``: for every chunk of the M3 corpus (every chunk that carries a transaction or
  a receipt, and the first heights) the transactions and incoming receipts as Borsh, what nearcore
  returned as outgoing receipts, and the ``ApplyState`` context it used. A chunk absent from the
  file is empty: the block corpus checks the transaction root of every chunk header.

``run`` is ``just chain-apply-corpus``: it unpacks the corpus and runs ``node-chain-apply`` on each
topology; the exit code is 0 only when the epochs, the chunk results and the restart all agree.
"""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import chain_corpus
import corpus
import nearcodec as nc

ROOT = chain_corpus.ROOT
CHUNKS = ROOT / "near-lean/chain/corpus/chunks"
BINARY = ROOT / "near-lean/node/.lake/build/bin/node-chain-apply"


def u32(n: int) -> bytes:
    return n.to_bytes(4, "little")


def u64(n: int) -> bytes:
    return n.to_bytes(8, "little")


def string(s: str) -> bytes:
    raw = s.encode()
    return u32(len(raw)) + raw


def shard_layout_v2(layout: dict) -> bytes:
    """Borsh of ``ShardLayout::V2``."""
    body = layout["V2"]
    out = bytearray([2])
    out += u32(len(body["boundary_accounts"])) + b"".join(string(a) for a in body["boundary_accounts"])
    out += u32(len(body["shard_ids"])) + b"".join(u64(s) for s in body["shard_ids"])
    for name in ("id_to_index_map", "index_to_id_map"):
        rows = sorted((int(k), v) for k, v in body[name].items())
        out += u32(len(rows)) + b"".join(u64(k) + u64(v) for k, v in rows)
    for name in ("shards_split_map", "shards_parent_map"):
        if body[name] is not None:
            raise SystemExit(f"{name} is not represented")
        out += b"\0"
    out += u32(body["version"])
    return bytes(out)


def public_key(text: str) -> str:
    kind, body = text.split(":", 1)
    if kind != "ed25519":
        raise SystemExit(f"public key type {kind}")
    return (b"\0" + nc.b58decode(body)).hex()


def genesis_file(topology: str) -> dict:
    g = json.loads((chain_corpus.DATA / topology / "node0/genesis.json").read_text())
    records = []
    for row in g["records"]:
        kind, value = next(iter(row.items()))
        if kind == "Account":
            account = value["account"]
            records.append({"account": {
                "id": value["account_id"], "amount": account["amount"], "locked": account["locked"],
                "codeHash": nc.b58decode(account["code_hash"]).hex(), "storageUsage": account["storage_usage"],
                "version": account["version"]}})
        elif kind == "AccessKey":
            if value["access_key"]["permission"] != "FullAccess":
                raise SystemExit("genesis access key permission")
            records.append({"accessKey": {"id": value["account_id"], "publicKey": public_key(value["public_key"]),
                                          "nonce": value["access_key"]["nonce"]}})
        else:
            raise SystemExit(f"genesis record {kind}")
    return {
        "chainId": g["chain_id"], "protocolVersion": g["protocol_version"], "epochLength": g["epoch_length"],
        "numBlockProducerSeats": g["num_block_producer_seats"],
        "protocolRewardRate": g["protocol_reward_rate"], "protocolTreasuryAccount": g["protocol_treasury_account"],
        "numBlocksPerYear": g["num_blocks_per_year"], "totalSupply": g["total_supply"],
        "validators": [{"accountId": v["account_id"], "publicKey": public_key(v["public_key"]), "stake": v["amount"]}
                       for v in g["validators"]],
        "shardLayout": shard_layout_v2(g["shard_layout"]).hex(), "records": records,
    }


def chunk_rows(topology: str) -> list[dict]:
    rows = []
    for directory in sorted(CHUNKS.iterdir()):
        if not directory.name.startswith(topology + "-"):
            continue
        meta = json.loads((directory / "meta.json").read_text())
        bundle = corpus.unpack(directory)       # values of 1 KiB or more are stored once, by digest
        inputs, expected, context = bundle["inputs"], bundle["expected"], bundle["context"]
        rows.append({
            "height": meta["height"], "shardId": meta["shardId"],
            "transactions": [t["borsh"] for t in inputs["transactions"]],
            "incomingReceipts": inputs["incomingReceipts"], "outgoingReceipts": expected["outgoingReceipts"],
            "context": context})
    rows.sort(key=lambda r: (r["height"], r["shardId"]))
    return rows


def add_extras(corpus: Path) -> None:
    manifest = json.loads((corpus / "manifest.json").read_text())
    for topology, summary in manifest["topologies"].items():
        genesis = (json.dumps(genesis_file(topology), indent=1, sort_keys=True) + "\n").encode()
        (corpus / topology / "genesis.json").write_bytes(genesis)
        summary["files"]["genesis.json"] = {"bytes": len(genesis), "sha256": chain_corpus.sha256(genesis)}
        rows = chunk_rows(topology)
        raw = b"".join((json.dumps(r, sort_keys=True, separators=(",", ":")) + "\n").encode() for r in rows)
        packed = chain_corpus.gz(raw)
        (corpus / topology / "chunks.jsonl.gz").write_bytes(packed)
        summary["files"]["chunks.jsonl.gz"] = {"bytes": len(packed), "sha256": chain_corpus.sha256(packed),
                                               "rawSha256": chain_corpus.sha256(raw), "lines": len(rows)}
    manifest["totalBytes"] = sum(f["bytes"] for t in manifest["topologies"].values() for f in t["files"].values())
    (corpus / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def unpack(corpus: Path, destination: Path, topology: str) -> Path:
    target = chain_corpus.unpack(corpus, destination, topology)
    (target / "genesis.json").write_bytes((corpus / topology / "genesis.json").read_bytes())
    (target / "chunks.jsonl").write_bytes(gzip.decompress((corpus / topology / "chunks.jsonl.gz").read_bytes()))
    return target


def run(args: argparse.Namespace) -> None:
    problems = chain_corpus.check(args.corpus)
    if problems:
        print("\n".join(problems), file=sys.stderr)
        sys.exit(1)
    ok = True
    with tempfile.TemporaryDirectory(prefix="safe-near-apply-") as temporary:
        for topology in args.topologies:
            directory = unpack(args.corpus, Path(temporary), topology)
            command = [str(args.binary), str(directory)] + args.options
            result = subprocess.run(command, text=True)
            ok = ok and result.returncode == 0
    print("all agree" if ok else "DISAGREEMENT")
    sys.exit(0 if ok else 1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    e = sub.add_parser("extras", help="add genesis.json and chunks.jsonl.gz to the packed corpus")
    e.add_argument("--corpus", type=Path, default=chain_corpus.DEFAULT_CORPUS)
    r = sub.add_parser("run", help="run node-chain-apply on the corpus (just chain-apply-corpus)")
    r.add_argument("--corpus", type=Path, default=chain_corpus.DEFAULT_CORPUS)
    r.add_argument("--binary", type=Path, default=BINARY)
    r.add_argument("--topologies", nargs="*", default=list(chain_corpus.TOPOLOGIES))
    r.add_argument("options", nargs="*", help="passed to node-chain-apply (for example --max-height 100)")
    a = parser.parse_args()
    if a.command == "extras":
        add_extras(a.corpus)
    else:
        run(a)


if __name__ == "__main__":
    main()
