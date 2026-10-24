#!/usr/bin/env python3
"""The block corpus of the Lean chain validator (M5a): export, pack, unpack and check (stdlib only).

``export`` runs ``safe-near-chain-export`` (``chain_exporter.rs``, built by ``build.py``) on a copy
of a localnet database and writes, per topology, ``meta.json``, ``epochs.jsonl``, ``blocks.jsonl`` and
``variants.jsonl`` (formats in the header of the exporter and in CORPUS.md).  ``pack`` stores them
under ``near-lean/node/corpus/blocks/<topology>/`` (the JSONL files gzipped without timestamps, so the
packing is deterministic) with a ``manifest.json`` of counts, sizes and hashes.  ``unpack`` is the
inverse, and ``check`` verifies the committed files against the manifest and their internal
consistency without neard.
"""

from __future__ import annotations

import argparse
import collections
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_CORPUS = ROOT / "near-lean/node/corpus/blocks"
DATA = HERE / "data"
EXPORTER = HERE / "target/bin/safe-near-chain-export"
FORMAT = "safe-near-chain-corpus-v1"
TOPOLOGIES = ("single", "sharded")
JSONL = ("epochs", "blocks", "variants")
SIZE_BUDGET = 20 * 1024 * 1024
# validator keys of the nodes, which re-sign the variants (`validator_key.json` of each node)
NODES = {"single": ("node0",), "sharded": ("node0", "node1")}


def gz(data: bytes) -> bytes:
    return gzip.compress(data, compresslevel=9, mtime=0)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_lines(path: Path) -> list[dict]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as handle:
        return [json.loads(line) for line in handle if line.strip()]


# --- export -------------------------------------------------------------------
def export(topology: str, bases: int, seed: int) -> Path:
    """Run the exporter on a copy of the topology's first node; returns the raw output directory."""
    if not EXPORTER.exists():
        raise SystemExit(f"{EXPORTER} is missing: run `python3 tools/localnet/build.py --only safe-near-chain-export`")
    source = DATA / topology
    out = source / "chain"
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix="safe-near-chain-export-") as temporary:
        home = Path(temporary) / "node"
        shutil.copytree(source / NODES[topology][0], home)
        command = [str(EXPORTER), "--home", str(home), "--out", str(out), "--writable",
                   "--bases", str(bases), "--seed", str(seed)]
        for node in NODES[topology]:
            command += ["--key", str(source / node / "validator_key.json")]
        subprocess.run(command, check=True)
    return out


# --- pack ---------------------------------------------------------------------
def summarize(raw: Path) -> dict:
    meta = json.loads((raw / "meta.json").read_text())
    blocks = read_lines(raw / "blocks.jsonl")
    variants = read_lines(raw / "variants.jsonl")
    kinds = collections.Counter(v["name"] for v in variants)
    errors = collections.Counter(v["expected"]["error"] for v in variants)
    return {
        "chainId": meta["chainId"], "protocolVersion": meta["protocolVersion"], "genesisHash": meta["genesisHash"],
        "genesisHeight": meta["genesisHeight"], "headHeight": meta["headHeight"], "epochLength": meta["epochLength"],
        "blocks": len(blocks), "epochs": len(read_lines(raw / "epochs.jsonl")), "variants": len(variants),
        "variantKinds": dict(sorted(kinds.items())), "variantErrors": dict(sorted(errors.items())),
        "baseHeights": meta["baseHeights"],
    }


def pack(corpus: Path, raws: dict[str, Path]) -> dict:
    manifest = {"format": FORMAT, "topologies": {}}
    reference = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())
    build = json.loads((ROOT / "near-lean/chain/corpus/build.json").read_text())["neard"]
    manifest["sourceRevision"] = reference["revision"]
    manifest["release"] = reference["release"]
    manifest["neardVersion"] = build["neardVersion"].splitlines()[0]
    manifest["exporterSha256"] = sha256((HERE / "chain_exporter.rs").read_bytes())
    for topology, raw in raws.items():
        target = corpus / topology
        shutil.rmtree(target, ignore_errors=True)
        target.mkdir(parents=True)
        summary = summarize(raw)
        summary["validators"] = list(NODES[topology])
        files = {}
        meta_bytes = (raw / "meta.json").read_bytes()
        (target / "meta.json").write_bytes(meta_bytes)
        files["meta.json"] = {"bytes": len(meta_bytes), "sha256": sha256(meta_bytes)}
        for name in JSONL:
            data = (raw / f"{name}.jsonl").read_bytes()
            packed = gz(data)
            (target / f"{name}.jsonl.gz").write_bytes(packed)
            files[f"{name}.jsonl.gz"] = {"bytes": len(packed), "sha256": sha256(packed), "rawSha256": sha256(data),
                                         "lines": data.count(b"\n")}
        summary["files"] = files
        manifest["topologies"][topology] = summary
    manifest["totalBytes"] = sum(f["bytes"] for t in manifest["topologies"].values() for f in t["files"].values())
    (corpus / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest


# --- unpack and check ---------------------------------------------------------
def unpack(corpus: Path, destination: Path, topology: str) -> Path:
    """Decompress a topology into ``destination/<topology>``; returns that directory."""
    target = destination / topology
    target.mkdir(parents=True, exist_ok=True)
    source = corpus / topology
    shutil.copyfile(source / "meta.json", target / "meta.json")
    for name in JSONL:
        (target / f"{name}.jsonl").write_bytes(gzip.decompress((source / f"{name}.jsonl.gz").read_bytes()))
    return target


def check(corpus: Path) -> list[str]:
    """Problems found in a packed corpus (empty when it is well formed)."""
    problems: list[str] = []
    manifest = json.loads((corpus / "manifest.json").read_text())
    if manifest.get("format") != FORMAT:
        problems.append("manifest format")
    total = 0
    for topology, summary in manifest["topologies"].items():
        directory = corpus / topology
        for name, expected in summary["files"].items():
            data = (directory / name).read_bytes()
            total += len(data)
            if len(data) != expected["bytes"] or sha256(data) != expected["sha256"]:
                problems.append(f"{topology}/{name}: size or hash differs from the manifest")
            if name.endswith(".gz"):
                try:
                    raw = gzip.decompress(data)
                except (OSError, EOFError) as error:
                    problems.append(f"{topology}/{name}: not a gzip file ({error})")
                    continue
                if sha256(raw) != expected["rawSha256"] or raw.count(b"\n") != expected["lines"]:
                    problems.append(f"{topology}/{name}: content differs from the manifest")
        meta = json.loads((directory / "meta.json").read_text())
        if problems:
            continue
        blocks = read_lines(directory / "blocks.jsonl.gz")
        variants = read_lines(directory / "variants.jsonl.gz")
        epochs = read_lines(directory / "epochs.jsonl.gz")
        if len(blocks) != summary["blocks"] or len(variants) != summary["variants"] or len(epochs) != summary["epochs"]:
            problems.append(f"{topology}: counts differ from the manifest")
        # the blocks form a chain from genesis to the head
        if blocks[0]["hash"] != meta["genesisHash"] or not blocks[0]["isGenesis"]:
            problems.append(f"{topology}: the first block is not the genesis block")
        for earlier, later in zip(blocks, blocks[1:]):
            if later["prevHash"] != earlier["hash"] or later["height"] <= earlier["height"] or later["isGenesis"]:
                problems.append(f"{topology}: block {later['height']} does not extend block {earlier['height']}")
        if blocks[-1]["height"] != meta["headHeight"]:
            problems.append(f"{topology}: the last block is not the head")
        epoch_ids = {e["epochId"] for e in epochs}
        for block in blocks:
            for key in ("epochId", "nextEpochId"):
                if block["derived"][key] not in epoch_ids and block["height"] > 0:
                    problems.append(f"{topology}: block {block['height']} {key} has no EpochInfo")
        # every variant is a rejection of a block of the chain
        heights = {b["height"]: b for b in blocks}
        for variant in variants:
            base = heights.get(variant["baseHeight"])
            if base is None or base["hash"] != variant["baseHash"]:
                problems.append(f"{topology}: variant {variant['name']} has no base block")
            if variant["expected"].get("accepted") is not False or not variant["expected"].get("error"):
                problems.append(f"{topology}: variant {variant['name']} is not a recorded rejection")
            if variant["block"] == base["block"]:
                problems.append(f"{topology}: variant {variant['name']} equals its base")
    if total > SIZE_BUDGET:
        problems.append(f"corpus is {total} bytes, over the {SIZE_BUDGET} budget")
    return problems


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    e = sub.add_parser("export", help="run the exporter on data/<topology> (needs build.py --only safe-near-chain-export)")
    e.add_argument("topologies", nargs="*", default=list(TOPOLOGIES))
    e.add_argument("--bases", type=int, default=24, help="base blocks per chain for the invalid variants")
    e.add_argument("--seed", type=int, default=1)
    p = sub.add_parser("pack", help="pack data/<topology>/chain into the corpus")
    p.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    p.add_argument("topologies", nargs="*", default=list(TOPOLOGIES))
    u = sub.add_parser("unpack", help="decompress the corpus into a directory")
    u.add_argument("destination", type=Path)
    u.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    c = sub.add_parser("check", help="verify the packed corpus")
    c.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    a = parser.parse_args()
    if a.command == "export":
        for topology in a.topologies:
            print(f"exporting {topology}", flush=True)
            export(topology, a.bases, a.seed)
    elif a.command == "pack":
        manifest = pack(a.corpus, {t: DATA / t / "chain" for t in a.topologies})
        print(json.dumps({t: {k: v for k, v in s.items() if k in ("blocks", "epochs", "variants")}
                          for t, s in manifest["topologies"].items()}, indent=2), f"\n{manifest['totalBytes']} bytes")
    elif a.command == "unpack":
        for topology in TOPOLOGIES:
            unpack(a.corpus, a.destination, topology)
    else:
        problems = check(a.corpus)
        for problem in problems:
            print(problem, file=sys.stderr)
        sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
