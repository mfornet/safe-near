#!/usr/bin/env python3
"""Corpus bundles: packing, unpacking, feature tags, selection and result comparison (stdlib only).

A *raw bundle* is the single JSON document the exporter writes and the oracle checker reads
(see CORPUS.md).  A *packed chunk* is the same data split into a directory of files, with
large values replaced by content-addressed blobs shared by the whole corpus.  ``unpack`` is the
exact inverse of ``pack``.  Packing is deterministic: sorted keys, no timestamps in gzip.
"""

from __future__ import annotations

import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_CORPUS = ROOT / "near-lean/chain/corpus"
BLOB_THRESHOLD = 1024          # bytes: values at least this long are stored once, by hash
FORMAT = "safe-near-corpus-v1"

# column bytes of raw trie keys (core/primitives/src/trie_key.rs)
COLUMN_NAMES = {0: "account", 1: "contract-code", 2: "access-key", 3: "received-data", 4: "postponed-receipt-id",
                5: "pending-data-count", 6: "postponed-receipt", 7: "delayed-receipt", 9: "contract-data",
                10: "promise-yield-indices", 11: "promise-yield-timeout", 12: "promise-yield-receipt",
                13: "buffered-receipt-indices", 14: "buffered-receipt", 15: "bandwidth-scheduler-state",
                16: "buffered-receipt-groups-data", 17: "buffered-receipt-groups-item",
                18: "global-contract-code", 19: "global-contract-nonce", 20: "promise-yield-status",
                22: "yield-id-to-data-id", 23: "data-id-to-yield-id"}


def dumps(value, *, indent=None) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=indent, separators=None if indent else (",", ":")) + "\n").encode()


def gz(data: bytes) -> bytes:
    # The header's OS byte depends on the Python version (3 on 3.12, 255 on 3.13); pin it to 255.
    packed = bytearray(gzip.compress(data, compresslevel=9, mtime=0))
    packed[9] = 0xFF
    return bytes(packed)


# --- packing ------------------------------------------------------------------
def chunk_name(bundle: dict, topology: str) -> str:
    meta = bundle["meta"]
    return f"{topology}-h{meta['height']:08d}-s{meta['shardId']}"


def pack_decoded(directory: Path, corpus: Path, decoded: dict) -> None:
    """Store the pinned decoders' readable projection of the pre-state next to the raw entries."""
    def code_to_blob(text):
        if not isinstance(text, str) or len(text) < BLOB_THRESHOLD * 4 // 3:
            return text
        raw = base64.b64decode(text, validate=True)
        digest = hashlib.sha256(raw).hexdigest()
        path = corpus / "blobs" / f"{digest}.bin.gz"
        if not path.exists():
            path.write_bytes(gz(raw))
        return {"blob": digest}

    (directory / "decoded.json.gz").write_bytes(gz(dumps(transform_code(decoded, code_to_blob))))


def pack(bundle: dict, topology: str, corpus: Path) -> str:
    """Write one chunk under ``corpus/chunks``; returns its name.  Large values go to ``corpus/blobs``."""
    name = chunk_name(bundle, topology)
    directory = corpus / "chunks" / name
    directory.mkdir(parents=True, exist_ok=True)
    blobs = corpus / "blobs"
    blobs.mkdir(exist_ok=True)

    def blobify(hex_value: str):
        raw = bytes.fromhex(hex_value)
        if len(raw) < BLOB_THRESHOLD:
            return hex_value
        digest = hashlib.sha256(raw).hexdigest()
        path = blobs / f"{digest}.bin.gz"
        if not path.exists():
            path.write_bytes(gz(raw))
        return {"blob": digest}

    meta = dict(bundle["meta"], topology=topology, format=FORMAT)
    (directory / "meta.json").write_bytes(dumps(meta, indent=1))
    (directory / "context.json").write_bytes(dumps(bundle["context"], indent=1))
    pre = bundle["preState"]
    entries = [[key, blobify(value)] for key, value in pre["entries"]]
    (directory / "pre_state.json.gz").write_bytes(gz(dumps({"root": pre["root"], "entries": entries})))
    inputs = json.loads(json.dumps(bundle["inputs"]))
    def code_to_blob(text):
        if not isinstance(text, str) or len(text) < BLOB_THRESHOLD * 4 // 3:
            return text
        raw = base64.b64decode(text, validate=True)
        if base64.b64encode(raw).decode() != text:
            return text
        return blobify(raw.hex())

    for row in inputs["transactions"]:
        row["borsh"] = blobify(row["borsh"])
        row["view"] = transform_code(row["view"], code_to_blob)
        row["actions"] = transform_code(row["actions"], code_to_blob)
    inputs["incomingReceiptViews"] = transform_code(inputs["incomingReceiptViews"], code_to_blob)
    inputs["incomingReceiptTyped"] = transform_code(inputs["incomingReceiptTyped"], code_to_blob)
    (directory / "inputs.json.gz").write_bytes(gz(dumps(inputs)))
    expected = json.loads(json.dumps(bundle["expected"]))
    expected["stateDiff"] = [[key, None if value is None else blobify(value)] for key, value in expected["stateDiff"]]
    expected["outgoingReceiptViews"] = transform_code(expected["outgoingReceiptViews"], code_to_blob)
    (directory / "expected.json.gz").write_bytes(gz(dumps(expected)))
    return name


def transform_code(value, convert):
    """Copy of a JSON view with every ``code`` string (deployed Wasm in base64) passed through ``convert``."""
    if isinstance(value, dict):
        return {key: convert(child) if key == "code" else transform_code(child, convert) for key, child in value.items()}
    if isinstance(value, list):
        return [transform_code(child, convert) for child in value]
    return value


def read_blob(corpus: Path, digest: str) -> bytes:
    raw = gzip.decompress((corpus / "blobs" / f"{digest}.bin.gz").read_bytes())
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError(f"blob {digest} is corrupt")
    return raw


def unblob(corpus: Path, value):
    return value if isinstance(value, str) or value is None else read_blob(corpus, value["blob"]).hex()


def unpack(directory: Path, corpus: Path | None = None) -> dict:
    """Rebuild the raw bundle of a packed chunk directory."""
    corpus = corpus or directory.parent.parent
    meta = json.loads((directory / "meta.json").read_text())
    pre = json.loads(gzip.decompress((directory / "pre_state.json.gz").read_bytes()))
    inputs = json.loads(gzip.decompress((directory / "inputs.json.gz").read_bytes()))
    expected = json.loads(gzip.decompress((directory / "expected.json.gz").read_bytes()))
    def blob_to_code(value):
        return value if isinstance(value, str) else base64.b64encode(read_blob(corpus, value["blob"])).decode()

    for row in inputs["transactions"]:
        row["borsh"] = unblob(corpus, row["borsh"])
        row["view"] = transform_code(row["view"], blob_to_code)
        row["actions"] = transform_code(row["actions"], blob_to_code)
    inputs["incomingReceiptViews"] = transform_code(inputs["incomingReceiptViews"], blob_to_code)
    inputs["incomingReceiptTyped"] = transform_code(inputs["incomingReceiptTyped"], blob_to_code)
    expected["outgoingReceiptViews"] = transform_code(expected["outgoingReceiptViews"], blob_to_code)
    expected["stateDiff"] = [[key, unblob(corpus, value)] for key, value in expected["stateDiff"]]
    meta = {k: v for k, v in meta.items() if k not in ("topology", "format")}
    decoded = None
    if (directory / "decoded.json.gz").exists():
        decoded = json.loads(gzip.decompress((directory / "decoded.json.gz").read_bytes()))
        decoded = transform_code(decoded, blob_to_code)
    return {
        "formatVersion": 1, "meta": meta, "decoded": decoded,
        "context": json.loads((directory / "context.json").read_text()),
        "preState": {"root": pre["root"], "entries": [[key, unblob(corpus, value)] for key, value in pre["entries"]]},
        "inputs": inputs, "expected": expected,
    }


# --- feature tags -------------------------------------------------------------
def action_kinds(actions) -> list[str]:
    kinds = []
    for action in actions:
        if action == "CreateAccount":
            kinds.append("CreateAccount")
        elif isinstance(action, dict):
            kinds.extend(action)
            for payload in action.values():
                if isinstance(payload, dict) and "delegate_action" in payload:
                    kinds.extend(action_kinds(payload["delegate_action"].get("actions", [])))
    return kinds


def host_function(cost: str) -> str:
    for suffix in ("_BASE", "_BYTE", "_ELEMENT", "_SUBLINEAR", "_MEMORY_BYTE", "_PER_BYTE"):
        if cost.endswith(suffix):
            cost = cost[: -len(suffix)]
            break
    return cost.lower()


def tags(bundle: dict) -> list[str]:
    result = set()
    context, inputs, expected = bundle["context"], bundle["inputs"], bundle["expected"]
    result.add("protocol:%d" % context["currentProtocolVersion"])
    for row in inputs["transactions"]:
        view = row["view"]
        result.add("tx")
        if not row["valid"]:
            result.add("tx:invalid")
        for kind in action_kinds(view.get("actions", [])):
            result.add("action:" + kind)
            result.add("tx-action:" + kind)
        if view.get("nonce_index") is not None:
            result.add("tx:gas-key-nonce")
        if view.get("nonce_mode") == "strict":
            result.add("tx:strict-nonce")
        if view["signer_id"] and len(view["signer_id"]) == 64:
            result.add("signer:near-implicit")
    for view in inputs["incomingReceiptViews"]:
        result.add("incoming-receipt")
        payload = view["receipt"]
        kind = next(iter(payload)) if isinstance(payload, dict) else payload
        result.add("receipt:" + kind)
        if kind == "Action":
            for action in action_kinds(payload["Action"].get("actions", [])):
                result.add("action:" + action)
            if payload["Action"].get("input_data_ids"):
                result.add("receipt:callback")
        if view["predecessor_id"] == "system":
            result.add("receipt:system")
    for view in expected.get("outgoingReceiptViews", []):
        result.add("outgoing-receipt")
        payload = view["receipt"]
        kind = next(iter(payload)) if isinstance(payload, dict) else payload
        result.add("outgoing:" + kind)
        if kind == "Action":
            for action in action_kinds(payload["Action"].get("actions", [])):
                result.add("outgoing-action:" + action)
    for outcome in expected["outcomes"]:
        view = outcome["view"]
        status = view["status"]
        if isinstance(status, dict):
            key = next(iter(status))
            result.add("status:" + key)
            if key == "Failure":
                failure = status["Failure"]
                result.add("failure:" + (next(iter(failure)) if isinstance(failure, dict) else str(failure)))
                if isinstance(failure, dict) and "ActionError" in failure:
                    error = failure["ActionError"]["kind"]
                    result.add("failure:" + (next(iter(error)) if isinstance(error, dict) else str(error)))
        else:
            result.add("status:" + status)
        if view["logs"]:
            result.add("logs")
        metadata = view.get("metadata") or {}
        for entry in metadata.get("gas_profile") or []:
            if entry.get("cost_category") == "WASM_HOST_COST":
                result.add("host:" + host_function(entry["cost"]))
            elif entry.get("cost_category") == "ACTION_COST":
                result.add("cost:" + entry["cost"].lower())
    if context["validatorAccountsUpdate"] is not None:
        result.add("epoch-start")
    if expected["delayedReceiptsCount"]:
        result.add("delayed-receipts")
    if expected["validatorProposals"] != "00000000":
        result.add("validator-proposals")
    if expected["processedYieldTimeouts"] != "00000000":
        result.add("yield-timeout")
    if len(context["congestionInfo"]) > 1:
        result.add("multi-shard")
    if any(not value.get("0") and False for value in []):
        pass
    result.add("shard-layout:%d" % len(context["congestionInfo"]))
    columns = {int(key[:2], 16) for key, _ in bundle["preState"]["entries"]}
    for column in columns:
        result.add("state-column:" + COLUMN_NAMES.get(column, str(column)))
    post = {int(key[:2], 16) for key, _ in expected["stateDiff"]}
    for column in post:
        result.add("state-change:" + COLUMN_NAMES.get(column, str(column)))
    if not inputs["transactions"] and not inputs["incomingReceipts"]:
        result.add("empty-chunk")
    return sorted(result)


# --- comparison ---------------------------------------------------------------
def first_difference(expected, actual, path="") -> str | None:
    """Path of the first differing field, comparing JSON values structurally."""
    if isinstance(expected, dict) and isinstance(actual, dict):
        for key in sorted(set(expected) | set(actual)):
            if key not in actual:
                return f"{path}.{key} (missing)"
            if key not in expected:
                return f"{path}.{key} (unexpected)"
            found = first_difference(expected[key], actual[key], f"{path}.{key}")
            if found:
                return found
        return None
    if isinstance(expected, list) and isinstance(actual, list):
        for index, (left, right) in enumerate(zip(expected, actual)):
            found = first_difference(left, right, f"{path}[{index}]")
            if found:
                return found
        if len(expected) != len(actual):
            return f"{path} (length {len(expected)} != {len(actual)})"
        return None
    return None if expected == actual else path or "."


# the fields the oracle recomputes and the order in which a difference is reported
ORACLE_FIELDS = ["outcomes", "outgoingReceipts", "postStateRoot", "stateDiff", "stateChanges", "gasUsed",
                 "balanceBurnt", "balanceStats", "validatorProposals", "congestionInfo", "bandwidthRequests",
                 "bandwidthSchedulerStateHash", "delayedReceiptsCount", "processedYieldTimeouts", "outcomeRoot",
                 "contractUpdates"]


def compare_oracle(expected: dict, actual: dict) -> str | None:
    for field in ORACLE_FIELDS:
        if field not in actual:
            return f"{field} (missing from the oracle output)"
        if field == "outcomes":
            left = [{"id": o["id"], "borsh": o["borsh"], "computeUsage": o["computeUsage"]} for o in expected[field]]
            right = [{"id": o["id"], "borsh": o["borsh"], "computeUsage": o["computeUsage"]} for o in actual[field]]
            found = first_difference(left, right, field)
        else:
            found = first_difference(expected.get(field), actual[field], field)
        if found:
            return found
    return None


# --- oracle -------------------------------------------------------------------
def checker_binary() -> Path:
    return HERE / "target/bin/safe-near-corpus-check"


def run_oracle(bundle: dict, binary: Path | None = None) -> dict:
    with tempfile.TemporaryDirectory(prefix="safe-near-corpus-") as temporary:
        path = Path(temporary) / "bundle.json"
        path.write_bytes(dumps(bundle))
        result = subprocess.run([str(binary or checker_binary()), str(path)], capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "oracle failed")
    return json.loads(result.stdout)


def checker_decode(bundle: dict, binary: Path | None = None) -> dict:
    """The pre-state as upstream's own decoders read it (``safe-near-corpus-check --decode``)."""
    with tempfile.TemporaryDirectory(prefix="safe-near-decode-") as temporary:
        path = Path(temporary) / "bundle.json"
        path.write_bytes(dumps({k: v for k, v in bundle.items() if k != "decoded"}))
        result = subprocess.run([str(binary or checker_binary()), "--decode", str(path)], capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "decoder failed")
    return json.loads(result.stdout)


def chunk_dirs(corpus: Path) -> list[Path]:
    return sorted(path for path in (corpus / "chunks").iterdir() if path.is_dir())


def selfcheck(corpus: Path, only: list[str] | None = None) -> dict:
    """Re-apply every packed chunk with the pinned Runtime::apply; returns {chunk: None | difference}."""
    results = {}
    for directory in chunk_dirs(corpus):
        if only and directory.name not in only:
            continue
        bundle = unpack(directory, corpus)
        try:
            results[directory.name] = compare_oracle(bundle["expected"], run_oracle(bundle))
        except RuntimeError as error:
            results[directory.name] = f"oracle error: {error}"
    return results


# --- selection ----------------------------------------------------------------
# Features the committed corpus must show at least once (the build reports any that no chunk has).
REQUIRED_TAGS = [
    "action:CreateAccount", "action:Transfer", "action:DeployContract", "action:FunctionCall", "action:Stake",
    "action:AddKey", "action:DeleteKey", "action:DeleteAccount", "action:Delegate", "action:DeployGlobalContract",
    "action:UseGlobalContract", "action:TransferToGasKey", "action:WithdrawFromGasKey", "signer:near-implicit",
    "tx:strict-nonce", "receipt:Action", "receipt:Data", "receipt:callback", "receipt:system",
    "receipt:GlobalContractDistribution", "status:SuccessValue", "status:SuccessReceiptId", "status:Failure",
    "logs", "epoch-start", "validator-proposals", "delayed-receipts", "yield-timeout", "multi-shard",
    "shard-layout:1", "shard-layout:4", "state-change:promise-yield-receipt", "state-change:global-contract-code",
    "host:sha256", "host:keccak256", "host:ripemd160", "host:ed25519_verify", "host:ecrecover", "host:storage_write",
    "host:storage_read", "host:storage_remove", "host:alt_bn128_pairing_check", "host:bls12381_pairing",
    "host:validator_stake", "host:yield_create", "host:yield_resume", "host:promise_return",
]


def chunk_cost(directory: Path, corpus: Path) -> tuple[int, dict[str, int]]:
    """Bytes of the chunk's own files and the blobs it references (digest -> size)."""
    own = packed_size(directory)
    text = "".join(gzip.decompress((directory / name).read_bytes()).decode()
                   for name in ("pre_state.json.gz", "inputs.json.gz", "expected.json.gz"))
    blobs = {}
    for path in (corpus / "blobs").iterdir():
        digest = path.name.removesuffix(".bin.gz")
        if digest in text:
            blobs[digest] = path.stat().st_size
    return own, blobs


def select(entries: list[dict], budget: int, must=frozenset(), always=frozenset()) -> list[str]:
    """Pick chunks covering the most feature tags per byte, within ``budget`` bytes.

    ``entries`` rows have ``name``, ``size``, ``blobs`` (digest -> size) and ``tags``.  Names in ``always`` go
    first.  Tags in ``must`` count three times, tags carried by at most three chunks twice.  Blob bytes are charged
    once however many chosen chunks share them.  Deterministic: ties break on the name.
    """
    by_name = {entry["name"]: entry for entry in entries}
    frequency: dict[str, int] = {}
    for entry in entries:
        for tag in entry["tags"]:
            frequency[tag] = frequency.get(tag, 0) + 1
    covered: set[str] = set()
    paid: set[str] = set()
    chosen: list[str] = []
    spent = 0

    def take(entry):
        nonlocal spent
        spent += entry["size"] + sum(size for digest, size in entry["blobs"].items() if digest not in paid)
        paid.update(entry["blobs"])
        covered.update(entry["tags"])
        chosen.append(entry["name"])

    for name in sorted(always):
        if name in by_name:
            take(by_name[name])
    pool = [entry for entry in entries if entry["name"] not in chosen]
    while pool:
        best, best_score = None, 0.0
        for entry in pool:
            new = set(entry["tags"]) - covered
            if not new:
                continue
            weight = sum((3.0 if tag in must else 1.0) * (2.0 if frequency[tag] <= 3 else 1.0) for tag in new)
            cost = entry["size"] + sum(size for digest, size in entry["blobs"].items() if digest not in paid) + 2000
            score = weight / cost
            if best is None or score > best_score or (score == best_score and entry["name"] < best["name"]):
                best, best_score = entry, score
        if best is None:
            break
        extra = best["size"] + sum(size for digest, size in best["blobs"].items() if digest not in paid)
        if spent + extra > budget:
            pool.remove(best)
            continue
        take(best)
        pool.remove(best)
    # Then every remaining chunk that carries work (transactions or incoming receipts), smallest first.
    for entry in sorted((e for e in pool if {"tx", "incoming-receipt"} & set(e["tags"])), key=lambda e: (e["size"], e["name"])):
        extra = entry["size"] + sum(size for digest, size in entry["blobs"].items() if digest not in paid)
        if spent + extra <= budget:
            take(entry)
    return sorted(chosen)


def build_corpus(raw: dict[str, Path], destination: Path, budget: int = 20 * 1024 * 1024, early: int = 24) -> dict:
    """Pack every raw bundle, then keep a covering subset: the first ``early`` heights of each topology
    (state continuity from genesis, small and quick for the Lean replay) plus a greedy cover of the tags."""
    import shutil
    with tempfile.TemporaryDirectory(prefix="safe-near-stage-") as temporary:
        stage = Path(temporary)
        for topology, directory in sorted(raw.items()):
            for path in sorted(directory.glob("h*-s*/bundle.json")):
                pack(json.loads(path.read_text()), topology, stage)
        rows = []
        for directory in chunk_dirs(stage):
            bundle = unpack(directory, stage)
            own, blobs = chunk_cost(directory, stage)
            rows.append({"name": directory.name, "size": own, "blobs": blobs, "tags": tags(bundle),
                         "height": bundle["meta"]["height"]})
        always = {row["name"] for row in rows if row["height"] <= early}
        chosen = select(rows, budget, must=set(REQUIRED_TAGS), always=always)
        if destination.exists():
            shutil.rmtree(destination)
        (destination / "chunks").mkdir(parents=True)
        (destination / "blobs").mkdir()
        needed: set[str] = set()
        for row in rows:
            if row["name"] in chosen:
                shutil.copytree(stage / "chunks" / row["name"], destination / "chunks" / row["name"])
                needed.update(row["blobs"])
        for digest in sorted(needed):
            shutil.copyfile(stage / "blobs" / f"{digest}.bin.gz", destination / "blobs" / f"{digest}.bin.gz")
        for name in chosen:
            directory = destination / "chunks" / name
            bundle = unpack(directory, destination)
            pack_decoded(directory, destination, {"preState": checker_decode(bundle)["preState"]})
        covered = {tag for row in rows if row["name"] in chosen for tag in row["tags"]}
        return {"candidates": len(rows), "chosen": len(chosen), "missingRequiredTags": sorted(set(REQUIRED_TAGS) - covered)}


def packed_size(directory: Path) -> int:
    return sum(path.stat().st_size for path in directory.iterdir())


def manifest(corpus: Path, build: dict | None = None) -> dict:
    rows = []
    for directory in chunk_dirs(corpus):
        meta = json.loads((directory / "meta.json").read_text())
        bundle = unpack(directory, corpus)
        rows.append({
            "name": directory.name, "topology": meta["topology"], "height": meta["height"],
            "shardId": meta["shardId"], "protocolVersion": meta["protocolVersion"],
            "transactions": len(bundle["inputs"]["transactions"]),
            "incomingReceipts": len(bundle["inputs"]["incomingReceipts"]),
            "outcomes": len(bundle["expected"]["outcomes"]),
            "outgoingReceipts": len(bundle["expected"]["outgoingReceipts"]),
            "preStateEntries": len(bundle["preState"]["entries"]),
            "bytes": packed_size(directory), "tags": tags(bundle),
        })
    all_tags = sorted({tag for row in rows for tag in row["tags"]})
    coverage = {tag: sum(1 for row in rows if tag in row["tags"]) for tag in all_tags}
    return {"format": FORMAT, "build": build, "chunks": rows, "tagCoverage": coverage,
            "blobs": sorted(path.name for path in (corpus / "blobs").iterdir()) if (corpus / "blobs").exists() else []}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    pack_cmd = sub.add_parser("pack", help="pack raw exporter output into a corpus directory")
    pack_cmd.add_argument("raw", type=Path, help="directory of h*-s*/bundle.json")
    pack_cmd.add_argument("topology")
    pack_cmd.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    check_cmd = sub.add_parser("check", help="re-apply every chunk with the pinned Runtime::apply")
    check_cmd.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    check_cmd.add_argument("chunks", nargs="*")
    build_cmd = sub.add_parser("build", help="select chunks from raw bundles of both topologies into the corpus")
    build_cmd.add_argument("--raw", action="append", required=True, metavar="TOPOLOGY=DIR")
    build_cmd.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    build_cmd.add_argument("--budget-mb", type=float, default=20.0)
    manifest_cmd = sub.add_parser("manifest", help="rewrite manifest.json")
    manifest_cmd.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    arguments = parser.parse_args()
    if arguments.command == "pack":
        count = 0
        for path in sorted(arguments.raw.glob("h*-s*/bundle.json")):
            pack(json.loads(path.read_text()), arguments.topology, arguments.corpus)
            count += 1
        print(f"packed {count} chunks into {arguments.corpus}")
    elif arguments.command == "build":
        raw = {item.split("=", 1)[0]: Path(item.split("=", 1)[1]) for item in arguments.raw}
        report = build_corpus(raw, arguments.corpus, int(arguments.budget_mb * 1024 * 1024))
        print(json.dumps(report, indent=1))
        build = HERE / "target/bin/build.json"
        record = {"neard": json.loads(build.read_text()) if build.exists() else None, "workload": {}}
        for topology, directory in sorted(raw.items()):
            log = directory.parent / "workload.json"
            if log.exists():
                data = json.loads(log.read_text())
                record["workload"][topology] = {"seed": data["seed"], "lastHeight": data["lastHeight"],
                                                "transactions": len(data["transactions"])}
        (arguments.corpus / "build.json").write_bytes(dumps(record, indent=1))
        (arguments.corpus / "manifest.json").write_bytes(dumps(manifest(arguments.corpus, record), indent=1))
    elif arguments.command == "check":
        results = selfcheck(arguments.corpus, arguments.chunks)
        bad = {name: result for name, result in results.items() if result}
        for name, result in bad.items():
            print(f"FAIL {name}: {result}")
        print(f"{len(results) - len(bad)}/{len(results)} chunks reproduce bit for bit")
        sys.exit(1 if bad else 0)
    else:
        build = None
        path = arguments.corpus / "build.json"
        if path.exists():
            build = json.loads(path.read_text())
        (arguments.corpus / "manifest.json").write_bytes(dumps(manifest(arguments.corpus, build), indent=1))


if __name__ == "__main__":
    main()
