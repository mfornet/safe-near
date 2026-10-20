#!/usr/bin/env python3
"""Exercise contract state and callbacks through the captured-account chain bridge.

The complete corpus includes storage mutations, whose native trie-access gas
is not yet represented by the model. These remain real failing comparisons;
the report does not subtract or tolerate their differences.
"""
from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path
import tempfile

import import_snapshot as importer
from compare_fixture import compare
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference


METHODS = ["read", "fail", "spawn", "spawn_fail", "write", "remove", "panic_after_write"]
SCHEDULES = ["all", "idle", "callback-first", "data-first", "reverse", "delayed", "unfinished"]


def snapshot(version=86):
    blob = (HERE / "fixtures/stateful.wasm").read_bytes()
    config = json.loads((ROOT / f"near-lean/vm/configs/runtime_config_v{version}.json").read_text())
    accounts = []
    for identifier in ["captured.near", "callee.near"]:
        accounts.append(dict(account_id=identifier, account=dict(amount=str(10 * 10**24), locked="0",
            code_hash=importer.code_hash(blob), storage_usage=len(blob) + 228, storage_paid_at=0),
            code=dict(hash=importer.code_hash(blob), code_base64=base64.b64encode(blob).decode()),
            access_keys=[dict(public_key="ed25519:" + "1" * 32, access_key=dict(nonce=0, permission="FullAccess"))],
            gas_key_nonces=[], storage=dict(complete=True, prefixes_base64=[""],
                values=[dict(key="aw==", value="aGVsbG8=")])) )
    return dict(format="safe-near-snapshot-v1", source="offline synthetic contract fixture; no RPC capture",
        block=dict(header=dict(hash="1" * 32, height=100)),
        protocol_config=dict(protocol_version=version, runtime_config={k: v for k, v in config.items()
            if k not in {"runtime_finance", "runtime_admission"}}), accounts=accounts)


def block(height, transactions=(), incoming=None, gas_limit=None):
    return dict(blockHeight=height, blockTimestamp=height * 10**9, epochHeight=0, gasPrice="100000000",
        gasLimit=gas_limit, randomSeed=[0] * 32, prevBlockHash=[0] * 32,
        incomingIndices=incoming, transactions=list(transactions))


def scenario(method="spawn", schedule="all"):
    if method not in METHODS or schedule not in SCHEDULES:
        raise ValueError("unknown contract method or schedule")
    if schedule in {"callback-first", "data-first", "reverse", "delayed"} and method not in {"spawn", "spawn_fail"}:
        raise ValueError("this schedule requires a callback scenario")
    tx = dict(receiverId="captured.near", nonce=1, actions=[{"FunctionCall": {
        "method_name": method, "args": "", "gas": 150 * 10**12, "deposit": "0"}}])
    blocks = [block(101, [tx]), block(102)]
    if schedule == "callback-first":
        blocks += [block(103, incoming=[1]), block(104, incoming=[0]), block(105, incoming=[]),
                   block(106, incoming=[2]), block(107), block(108)]
    elif schedule == "data-first":
        blocks += [block(103, incoming=[0]), block(104, incoming=[3]), block(105, incoming=[0]), block(106), block(107)]
    elif schedule == "reverse":
        blocks += [block(103, incoming=[2, 1, 0]), block(104), block(105), block(106)]
    elif schedule == "delayed":
        blocks += [block(103, gas_limit=0), block(104), block(105), block(106), block(107)]
    elif schedule == "idle":
        blocks += [block(103, incoming=[]), block(104), block(105), block(106), block(107)]
    elif schedule != "unfinished":
        blocks += [block(i) for i in range(103, 109)]
    return dict(caller=dict(accountId="fixture-caller.near", seed="safe-near-stateful-chain", amount=str(100 * 10**24)), blocks=blocks)


def run_case(version, method, schedule, directory, reference, model):
    request = scenario(method, schedule)
    if schedule == "delayed":
        # Congestion metadata is an external chunk input. Carry its native
        # previous output explicitly, rather than resetting nonempty queue gas
        # to zero and causing an underflow when delayed receipts are removed.
        with tempfile.TemporaryDirectory(prefix="safe-near-context-plan-") as temporary:
            planning = Path(temporary) / "fixture"
            importer.prepare(snapshot(version), planning, reference=reference, model=model, scenario=request)
            source = json.loads((planning / "native.json").read_text())
            original = source["blocks"]
            source["blocks"] = []
            previous = None
            with frozen_reference(reference) as (native, _):
                for block, scenario_block in zip(original, request["blocks"]):
                    if previous is not None:
                        block["congestionInfo"] = previous
                        scenario_block["congestionInfo"] = previous
                    source["blocks"].append(block)
                    trace = importer.execute(native, source, planning)
                    if trace["stop"] != "blocksExhausted" or trace["unrunBlocks"]:
                        raise ValueError(f"native context planning failed: {trace['stop']}")
                    previous = trace["blocks"][-1]["nextCongestionInfo"]
    importer.prepare(snapshot(version), directory, reference=reference, model=model, scenario=request)
    return compare(directory, reference, model)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/contract-chain-comparison.json")
    parser.add_argument("--protocol", type=int, action="append", choices=[83, 84, 85, 86])
    parser.add_argument("--method", action="append", choices=METHODS)
    parser.add_argument("--schedule", action="append", choices=SCHEDULES)
    args = parser.parse_args()
    cases = []
    with tempfile.TemporaryDirectory(prefix="safe-near-contract-corpus-") as temporary:
        for version in args.protocol or [83, 84, 85, 86]:
            for method in args.method or METHODS:
                schedules = args.schedule or (SCHEDULES if method in {"spawn", "spawn_fail"} else ["all"])
                for schedule in schedules:
                    report = run_case(version, method, schedule, Path(temporary) / str(len(cases)), args.reference.resolve(), args.model.resolve())
                    cases.append(dict(protocolVersion=version, method=method, schedule=schedule, **report))
                    print(f"v{version} {method}/{schedule}: {len(report['differences'])} differences", flush=True)
    failed = sum(bool(case["differences"]) for case in cases)
    atomic_write(args.report.resolve(), (json.dumps(dict(cases=cases, differingCases=failed), indent=2) + "\n").encode())
    print(f"{len(cases)} contract cases, {failed} differed; evidence: {args.report.resolve()}")
    raise SystemExit(bool(failed))


if __name__ == "__main__":
    main()
