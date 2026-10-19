#!/usr/bin/env python3
"""Smoke-test the independent Runtime::apply oracle, not Lean equivalence."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from prepare import HERE, ROOT, atomic_write, digest


def file_digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def execute(binary: Path, request: dict) -> dict:
    process = subprocess.run([str(binary)], input=json.dumps(request), text=True,
                             capture_output=True, check=True)
    return json.loads(process.stdout)


def account(state: dict, identifier: str) -> dict:
    for row in state["decodedRecords"]:
        value = row.get("record", {}).get("Account")
        if value and value["account_id"] == identifier:
            return value["account"]
    raise AssertionError(f"missing account: {identifier}")


def probe(binary: Path) -> dict:
    build = json.loads(binary.with_name(binary.name + ".build.json").read_text())
    pin = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())
    expected_adapter = digest((HERE / "reference.rs").read_bytes())
    if (build.get("sourceRevision") != pin["revision"] or not build.get("sourceImplementationClean")
            or build.get("shimSha256") != expected_adapter or build.get("checkOnly") is not False):
        raise ValueError("runtime oracle build metadata is stale or incomplete; rebuild it")
    with tempfile.TemporaryDirectory(prefix="safe-near-apply-probe-") as directory:
        frozen = Path(directory) / "near-apply-reference"
        shutil.copy2(binary, frozen)
        if file_digest(frozen) != build.get("binarySha256"):
            raise ValueError("runtime oracle binary does not match its build metadata")
        runtime = json.loads(subprocess.check_output([str(frozen), "--metadata"], text=True))
        if runtime != build["runtime"]:
            raise ValueError("runtime oracle self-identification does not match its build metadata")
        request = json.loads(subprocess.check_output([str(frozen), "--example"], text=True))
        trace = execute(frozen, request)
        checks = []

        def require(name, condition):
            if not condition:
                raise AssertionError(f"runtime oracle smoke failed: {name}")
            checks.append(name)

        require("all six source-runtime applies succeed",
                trace["stop"] == "blocksExhausted" and trace["unrunBlocks"] == 0
                and len(trace["blocks"]) == 6)
        blocks = trace["blocks"]
        require("decoded transactions retain their canonical native bytes and versions",
                all([item["borsh"] for item in block["inputs"]["transactions"]] == source["transactions"]
                    for block, source in zip(blocks, request["blocks"]))
                and blocks[0]["inputs"]["transactions"][0]["version"] == 0
                and blocks[0]["inputs"]["transactions"][0]["view"]["signer_id"] == "alice.near"
                and blocks[0]["inputs"]["transactions"][0]["view"]["receiver_id"] == "bob.near")
        require("decoded incoming views preserve the selected native receipt frontier",
                trace["initialPendingReceiptViews"] == []
                and blocks[0]["inputs"]["incomingReceipts"] == []
                and blocks[1]["inputs"]["incomingReceipts"] == []
                and blocks[2]["inputs"]["incomingReceipts"] == blocks[0]["outgoingReceipts"])
        initial_bob = account(trace["initialState"], "bob.near")
        require("transaction acceptance defers the cross-account receipt",
                len(blocks[0]["outcomes"]) == 1 and len(blocks[0]["outgoingReceipts"]) == 1
                and account(blocks[0]["state"], "bob.near") == initial_bob)
        require("an explicit idle delivery leaves the receiver unchanged",
                blocks[1]["outcomes"] == [] and account(blocks[1]["state"], "bob.near") == initial_bob
                and blocks[1]["pendingReceipts"] == blocks[0]["pendingReceipts"])
        require("receipt delivery credits the receiver in the later chunk",
                int(account(blocks[2]["state"], "bob.near")["amount"]) == 11 * 10 ** 24
                and [item["outcome"]["executor_id"] for item in blocks[2]["outcomes"]] == ["bob.near"])
        require("signer-is-receiver actions execute in their transaction chunk",
                len(blocks[4]["outcomes"]) == 2
                and all(item["outcome"]["executor_id"] == "alice.near" for item in blocks[4]["outcomes"]))
        require("every raw trie key remains represented, including opaque shard state",
                all({tuple(key) for key, _ in block["state"]["entries"]}
                    == {tuple(row["key"]) for row in block["state"]["decodedRecords"]}
                    for block in blocks)
                and any(row.get("opaque") for row in blocks[0]["state"]["decodedRecords"]))
        repeated = execute(frozen, request)
        require("the complete native trace is reproducible", repeated == trace)
        continuation = copy.deepcopy(request)
        continuation["initialEntries"] = blocks[0]["state"]["entries"]
        continuation["pendingReceipts"] = blocks[0]["pendingReceipts"]
        continuation["blocks"] = request["blocks"][1:]
        resumed = execute(frozen, continuation)
        require("the complete raw trie and pending queue reproduce every later block",
                resumed["initialState"] == blocks[0]["state"]
                and resumed["initialPendingReceiptViews"] == blocks[0]["outgoingReceipts"]
                and resumed["blocks"] == blocks[1:] and resumed["unrunBlocks"] == 0)
        rejected = []
        for positions in ([0, 0], [2], [-1]):
            invalid = copy.deepcopy(request)
            invalid["blocks"][2]["incomingIndices"] = positions
            result = execute(frozen, invalid)
            require(f"invalid delivery {positions} is atomic and stops later blocks",
                    result["stop"] == "invalidSchedule" and result["unrunBlocks"] == 3
                    and result["blocks"][2]["state"] == blocks[1]["state"]
                    and result["blocks"][2]["pendingReceipts"] == blocks[1]["pendingReceipts"])
            rejected.append({"positions": positions, "trace": result})
        malformed = copy.deepcopy(request)
        malformed["blocks"][0]["transactions"][0] = [0]
        invalid_bytes = subprocess.run([str(frozen)], input=json.dumps(malformed), text=True, capture_output=True)
        require("malformed transaction Borsh fails instead of becoming a successful empty trace",
                invalid_bytes.returncode != 0 and not invalid_bytes.stdout.strip())
        return {"formatVersion": 1, "scope": "native-reference-smoke; no Lean comparison",
                "build": build, "checks": checks, "request": request, "trace": trace,
                "continuation": resumed, "rejectedSchedules": rejected,
                "malformedTransaction": {"exitCode": invalid_bytes.returncode, "stderr": invalid_bytes.stderr}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/chain-reference-smoke.json")
    arguments = parser.parse_args()
    report = probe(arguments.binary.resolve())
    atomic_write(arguments.report.resolve(), (json.dumps(report, indent=2) + "\n").encode())
    print(f"Runtime::apply reference smoke: {len(report['checks'])} checks passed.")
    print(f"Evidence: {arguments.report.resolve()}")


if __name__ == "__main__":
    main()
