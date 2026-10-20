#!/usr/bin/env python3
"""Compare ordinary function-call key admission and failure precedence."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import tempfile

from compare_fixture import compare
from contract_probe import snapshot, block
import import_snapshot as importer
from prepare import HERE, ROOT, atomic_write

CALLER = "fixture-caller.near"
BALANCE = str(100 * 10**24)
KEY = dict(nonce=0, permission={"FunctionCall": {
    "allowance": str(10**24), "receiver_id": "captured.near", "method_names": ["read"]}})


def transaction(method="read", receiver="captured.near", deposit="0"):
    return dict(receiverId=receiver, nonce=1, actions=[{"FunctionCall": {
        "method_name": method, "args": "", "gas": 10**12, "deposit": deposit}}])


CASES = ["finite", "unlimited", "any-method", "missing-key", "receiver", "method", "deposit",
    "deposit-before-receiver", "deposit-before-method", "requires-full", "multiple-actions", "allowance",
    "allowance-before-permission", "balance-before-allowance", "balance-before-permission",
    "storage-before-permission", "allowance-before-storage", "accepted-around-rejected"]


def prepare_case(version, name):
    key, tx, balance = copy.deepcopy(KEY), transaction(), BALANCE
    expected = None
    permission = key["permission"]["FunctionCall"]
    if name == "unlimited":
        permission["allowance"] = None
    elif name == "any-method":
        permission["method_names"] = []
    elif name == "missing-key":
        key, expected = None, "AccessKeyNotFound"
    elif name == "receiver":
        tx["receiverId"], expected = "other.near", "ReceiverMismatch"
    elif name == "method":
        tx = transaction("not_allowed")
        expected = "MethodNameMismatch"
    elif name.startswith("deposit"):
        tx = transaction("not_allowed" if name.endswith("method") else "read",
            "other.near" if name.endswith("receiver") else "captured.near", "1")
        expected = "DepositWithFunctionCall"
    elif name in {"requires-full", "multiple-actions"}:
        tx["actions"] = [{"Transfer": {"deposit": "1"}}] if name == "requires-full" else tx["actions"] * 2
        expected = "RequiresFullAccess"
    elif name.startswith("allowance"):
        permission["allowance"], expected = "0", "NotEnoughAllowance"
        if name.endswith("permission"):
            tx = transaction("not_allowed")
        if name.endswith("storage"):
            balance = str(10**22)
    elif name.startswith("balance"):
        balance, expected = "0", "notEnoughBalance"
        if name.endswith("allowance"):
            permission["allowance"] = "0"
        else:
            tx = transaction("not_allowed")
    elif name == "storage-before-permission":
        balance, tx, expected = str(10**22), transaction("not_allowed"), "lackBalanceForState"
    if name.endswith("storage") or name == "storage-before-permission":
        permission["method_names"].append("padding" * 200)
    txs = [tx]
    if name == "accepted-around-rejected":
        txs = [tx, dict(transaction("not_allowed"), nonce=2), dict(transaction(), nonce=2)]
        expected = "MethodNameMismatch"
    caller = dict(accountId=CALLER, seed="safe-near-permission-corpus", amount=balance, accessKey=key)
    scenario = dict(caller=caller, blocks=[block(101, txs)] + [block(i) for i in range(102, 106)])
    return snapshot(version), scenario, expected


def run_case(version, name, target, reference, model):
    capture, scenario, _ = prepare_case(version, name)
    importer.prepare(capture, target, reference=reference, model=model, scenario=scenario)
    return compare(target, reference, model)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=int, action="append", choices=[83, 84, 85, 86])
    parser.add_argument("--case", action="append", choices=CASES)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/permission-chain-comparison.json")
    args = parser.parse_args()
    cases = []
    with tempfile.TemporaryDirectory(prefix="safe-near-permissions-") as temporary:
        for version in args.protocol or [83, 84, 85, 86]:
            for name in args.case or CASES:
                report = run_case(version, name, Path(temporary) / str(len(cases)), args.reference.resolve(), args.model.resolve())
                cases.append(dict(protocolVersion=version, scenario=name, comparison=report))
                print(f"v{version} {name}: {len(report['differences'])} differences; projection={report['projectionError']}", flush=True)
    failed = sum(bool(case["comparison"]["differences"]) for case in cases)
    atomic_write(args.report.resolve(), (json.dumps(dict(cases=cases, differingCases=failed), indent=2) + "\n").encode())
    print(f"{len(cases)} permission cases, {failed} differed; evidence: {args.report.resolve()}")
    raise SystemExit(bool(failed))


if __name__ == "__main__":
    main()
