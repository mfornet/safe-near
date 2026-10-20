#!/usr/bin/env python3
"""Compare stateless action admission with full native apply."""
from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path
import tempfile

from compare_fixture import compare
from contract_probe import snapshot, block
import import_snapshot as importer
from prepare import HERE, ROOT, atomic_write

CALLER = "fixture-caller.near"
KEY = "ed25519:" + "1" * 32
CASES = ["zero-gas", "zero-before-method", "method-byte-over", "method-byte-at-limit",
    "prepaid-over", "prepaid-at-limit", "prepaid-overflow", "delete-order", "action-count",
    "action-count-before-nonce", "actions-before-version", "deploy-count", "deploy-before-call",
    "key-method-bytes-over", "key-method-bytes-at-limit", "key-method-length-over", "key-method-length-at-limit",
    "key-invalid-receiver", "key-invalid-receiver-truncated", "key-length-before-total", "accepted-around-rejected"]
LARGE_CASES = ["arguments-over", "contract-size-over"]


def call(method="read", gas=10**12, args=b""):
    return {"FunctionCall": dict(method_name=method, args=base64.b64encode(args).decode(), gas=gas, deposit="0")}


def add_key(methods, receiver="captured.near"):
    return {"AddKey": dict(public_key=KEY, access_key=dict(nonce=0,
        permission={"FunctionCall": dict(allowance=None, receiver_id=receiver, method_names=methods)}))}


def oversized_module(limit):
    # A valid custom section grows code without executable instructions or data.
    size = limit + 1
    payload_size = size - 13
    value, encoded = payload_size, bytearray()
    while True:
        part, value = value & 127, value >> 7
        encoded.append(part | (128 if value else 0))
        if not value:
            break
    blob = b"\0asm\1\0\0\0\0" + bytes(encoded) + bytes(payload_size)
    if len(blob) != size:
        raise ValueError("unexpected custom-section length encoding")
    return blob


def prepare_case(version, name):
    capture = snapshot(version)
    limits = capture["protocol_config"]["runtime_config"]["wasm_config"]["limit_config"]
    gas_limit, method_limit = limits["max_total_prepaid_gas"], limits["max_length_method_name"]
    tx = dict(receiverId="captured.near", nonce=1, actions=[call()])
    expected, code_blobs = None, []
    if name in {"zero-gas", "zero-before-method", "actions-before-version"}:
        tx["actions"] = [call("x" * (method_limit + 1) if name == "zero-before-method" else "read", gas=0)]
        expected = "FunctionCallZeroAttachedGas"
        if name == "actions-before-version":
            tx.update(version=1, nonceMode="strict")
    elif name.startswith("method-byte"):
        tx["actions"] = [call("é" * (method_limit // 2) + "x" * (method_limit % 2 + name.endswith("over")))]
        expected = "FunctionCallMethodNameLengthExceeded" if name.endswith("over") else None
    elif name.startswith("prepaid"):
        gas = (2**64 - 1) if name.endswith("overflow") else gas_limit + name.endswith("over")
        tx["actions"] = [call(gas=gas)] * (2 if name.endswith("overflow") else 1)
        expected = "IntegerOverflow" if name.endswith("overflow") else "TotalPrepaidGasExceeded" if name.endswith("over") else None
    elif name == "delete-order":
        tx.update(receiverId=CALLER, actions=[{"DeleteAccount": {"beneficiary_id": "captured.near"}}, {"Transfer": {"deposit": "1"}}])
        expected = "DeleteActionMustBeFinal"
    elif name.startswith("action-count"):
        tx["actions"] = [{"Transfer": {"deposit": "1"}}] * (limits["max_actions_per_receipt"] + 1)
        if name.endswith("nonce"):
            tx["nonce"] = 0
        expected = "TotalNumberOfActionsExceeded"
    elif name.startswith("deploy"):
        blob = capture["accounts"][0]["code"]["code_base64"]
        tx.update(receiverId=CALLER, actions=[{"DeployContract": {"code": blob}}] * 11)
        if name == "deploy-before-call":
            tx["actions"].append(call(gas=0))
        expected = "TotalNumberOfDeployActionsExceeded" if limits["max_deploy_actions_per_receipt"] < 11 else (
            "FunctionCallZeroAttachedGas" if name == "deploy-before-call" else None)
    elif name.startswith("key-"):
        methods, receiver = [], "captured.near"
        if name.startswith("key-method-bytes"):
            methods = [""] * (limits["max_number_bytes_method_names"] + name.endswith("over"))
            expected = "AddKeyMethodNamesNumberOfBytesExceeded" if name.endswith("over") else None
        elif name.startswith("key-method-length"):
            methods = ["é" * (method_limit // 2) + "x" * (method_limit % 2 + name.endswith("over"))]
            expected = "AddKeyMethodNameLengthExceeded" if name.endswith("over") else None
        elif name == "key-length-before-total":
            methods = ["x" * method_limit] * 8 + ["x" * (method_limit + 1)]
            expected = "AddKeyMethodNameLengthExceeded"
        else:
            receiver = "a" * 127 + "éZ" if name.endswith("truncated") else "UPPER.near"
            expected = "InvalidAccountId"
        tx.update(receiverId=CALLER, actions=[add_key(methods, receiver)])
    elif name == "arguments-over":
        tx["actions"] = [call(args=bytes(limits["max_arguments_length"] + 1))]
        expected = "FunctionCallArgumentsLengthExceeded"
    elif name == "contract-size-over":
        encoded = base64.b64encode(oversized_module(limits["max_contract_size"])).decode()
        tx.update(receiverId=CALLER, actions=[{"DeployContract": {"code": encoded}}])
        code_blobs, expected = [encoded], "ContractSizeExceeded"
    txs = [tx]
    if name == "accepted-around-rejected":
        txs = [dict(receiverId="captured.near", nonce=1, actions=[call()]),
            dict(receiverId="captured.near", nonce=2, actions=[call(gas=0)]),
            dict(receiverId="captured.near", nonce=2, actions=[call()])]
        expected = "FunctionCallZeroAttachedGas"
    scenario = dict(caller=dict(accountId=CALLER, seed="safe-near-action-validation", amount=str(100 * 10**24)),
        blocks=[block(101, txs)] + [block(i) for i in range(102, 106)])
    if code_blobs:
        scenario["codeBlobs"] = code_blobs
    return capture, scenario, expected


def run_case(version, name, target, reference, model):
    capture, scenario, _ = prepare_case(version, name)
    importer.prepare(capture, target, reference=reference, model=model, scenario=scenario)
    return compare(target, reference, model)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=int, action="append", choices=[83, 84, 85, 86])
    parser.add_argument("--case", action="append", choices=CASES + LARGE_CASES)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/action-validation-comparison.json")
    args = parser.parse_args()
    cases = []
    with tempfile.TemporaryDirectory(prefix="safe-near-action-validation-") as temporary:
        for version in args.protocol or [83, 84, 85, 86]:
            for name in args.case or CASES:
                report = run_case(version, name, Path(temporary) / str(len(cases)), args.reference.resolve(), args.model.resolve())
                cases.append(dict(protocolVersion=version, scenario=name, comparison=report))
                print(f"v{version} {name}: {len(report['differences'])} differences; projection={report['projectionError']}", flush=True)
    failed = sum(bool(case["comparison"]["differences"]) for case in cases)
    atomic_write(args.report.resolve(), (json.dumps(dict(cases=cases, differingCases=failed), indent=2) + "\n").encode())
    print(f"{len(cases)} action-validation cases, {failed} differed; evidence: {args.report.resolve()}")
    raise SystemExit(bool(failed))


if __name__ == "__main__":
    main()
