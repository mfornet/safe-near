#!/usr/bin/env python3
"""Targeted transfer/account-creation gas/price differential checks, not general conformance.

Checks all represented state/receipt/outcome fields for a deliberately restricted
financial corpus. Native metadata/compute/trie columns remain recorded gaps.
"""
from __future__ import annotations

import argparse
import base64
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from prepare import HERE, ROOT, atomic_write, digest
from probe import execute, frozen_reference

ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def public_key(text):
    kind, encoded = text.split(":")
    n = 0
    for char in encoded:
        n = n * 58 + ALPHABET.index(char)
    raw = b"\0" * (len(encoded) - len(encoded.lstrip("1"))) + n.to_bytes((n.bit_length() + 7) // 8, "big")
    tag, size = {"ed25519": (0, 32), "secp256k1": (1, 64)}[kind]
    if len(raw) != size:
        raise ValueError("invalid native public key length")
    return [tag, *raw]


def simple_action(action):
    if action == "CreateAccount" or action == {"CreateAccount": {}}:
        return {"kind": "createAccount"}
    if not isinstance(action, dict) or list(action) != ["Transfer"]:
        raise ValueError("gas probe supports only transfers and account creation; use the general bridge for other actions")
    return {"kind": "transfer", "deposit": action["Transfer"]["deposit"]}


def state(native, next_id):
    result = dict(accounts=[], accessKeys=[], storage=[], postponed=[], pendingDataCount=[],
                  postponedByData=[], receivedData=[], delayed=[], nextId=next_id)
    for row in native["decodedRecords"]:
        if row.get("opaque"):
            continue  # Full raw bytes remain in evidence; these are a declared observation gap.
        record = row["record"]
        if list(record) == ["Account"]:
            value = record["Account"]
            account = value["account"]
            if account["code_hash"] != "1" * 32:
                raise ValueError("gas probe requires accounts without code")
            result["accounts"].append([value["account_id"], dict(amount=account["amount"],
                locked=account["locked"], storageUsage=account["storage_usage"], codeHash=None)])
        elif list(record) == ["AccessKey"]:
            value = record["AccessKey"]
            key = value["access_key"]
            if key["permission"] != "FullAccess":
                raise ValueError("gas probe requires full-access keys")
            result["accessKeys"].append([[value["account_id"], public_key(value["public_key"])],
                dict(nonce=key["nonce"], permission=dict(kind="fullAccess"))])
        else:
            raise ValueError(f"unsupported state record in financial probe: {list(record)}")
    return result


def canonical_state(value):
    value = copy.deepcopy(value)
    for name in ("accounts", "accessKeys", "storage", "postponed", "pendingDataCount",
                 "postponedByData", "receivedData"):
        value[name].sort(key=lambda row: json.dumps(row[0], sort_keys=True))
    return value


def model_request(source, trace, config_dir):
    if source["pendingReceipts"] or any(row.get("opaque") for row in trace["initialState"]["decodedRecords"]):
        raise ValueError("probe requires a plain account/key genesis and empty delivery queue")
    result = dict(formatVersion=1, protocolVersion=source["protocolVersion"], configDir=str(config_dir),
                  codes=[], initialState=state(trace["initialState"], 1), pendingReceipts=[], blocks=[])
    for header, block in zip(source["blocks"], trace["blocks"]):
        value = {key: header[key] for key in ("blockHeight", "blockTimestamp", "epochHeight", "gasPrice",
                                            "gasLimit", "randomSeed", "incomingIndices")}
        transactions = []
        for row in block["inputs"]["transactions"]:
            tx = row["view"]
            if row["version"] != 0:
                raise ValueError("probe requires V0 transactions")
            transactions.append(dict(signerId=tx["signer_id"], receiverId=tx["receiver_id"],
                publicKey=public_key(tx["public_key"]), nonce=tx["nonce"], actions=list(map(simple_action, tx["actions"]))))
        value["transactions"] = transactions
        result["blocks"].append(value)
    return result


def projection(source, trace):
    ids = {}
    pending, pending_borsh, blocks = [], [], []

    def existing(identifier):
        if identifier not in ids:
            raise ValueError(f"native receipt id has no earlier creation event: {identifier}")
        return ids[identifier]

    def receipt(value):
        payload = value["receipt"]
        if list(payload) != ["Action"]:
            raise ValueError("financial probe received a non-action receipt")
        action = payload["Action"]
        if action["input_data_ids"] or action["output_data_receivers"]:
            raise ValueError("financial probe received data dependencies")
        return dict(predecessorId=value["predecessor_id"], receiverId=value["receiver_id"],
            receiptId=existing(value["receipt_id"]), receipt=dict(kind="action",
                signerId=action["signer_id"], signerPublicKey=public_key(action["signer_public_key"]),
                gasPrice=action["gas_price"], inputDataIds=[], outputDataReceivers=[],
                actions=list(map(simple_action, action["actions"]))))

    for header, block in zip(source["blocks"], trace["blocks"]):
        tx_hashes = {row["view"]["hash"] for row in block["inputs"]["transactions"]}
        for outcome in block["outcomes"]:
            for identifier in outcome["outcome"]["receipt_ids"]:
                if identifier in ids:
                    raise ValueError("financial native runtime reused a created receipt id")
                ids[identifier] = len(ids) + 1
        positions = header["incomingIndices"]
        positions = list(range(len(pending))) if positions is None else positions
        if [pending[i] for i in positions] != block["inputs"]["incomingReceipts"]:
            raise ValueError("native decoded inputs disagree with selected pending receipts")
        pending = [value for i, value in enumerate(pending) if i not in positions] + block["outgoingReceipts"]
        pending_borsh = [value for i, value in enumerate(pending_borsh) if i not in positions] + block["outgoingReceiptBorsh"]
        if pending_borsh != block["pendingReceipts"] or block["delayedReceiptsCount"]:
            raise ValueError("native queue representation is outside the probe's supported transfer frontier")
        outcomes = []
        for row in block["outcomes"]:
            outcome = row["outcome"]
            status = outcome["status"]
            if list(status) == ["SuccessReceiptId"]:
                status = dict(kind="successReceiptId", receiptId=existing(status["SuccessReceiptId"]))
            elif list(status) == ["SuccessValue"]:
                status = dict(kind="successValue", value=list(base64.b64decode(status["SuccessValue"], validate=True)))
            else:
                raise ValueError("unexpected failure in successful financial probe")
            outcomes.append(dict(id=0 if row["id"] in tx_hashes else existing(row["id"]),
                outcome=dict(executorId=outcome["executor_id"], status=status, logs=outcome["logs"],
                    receiptIds=list(map(existing, outcome["receipt_ids"])), gasBurnt=outcome["gas_burnt"],
                    tokensBurnt=outcome["tokens_burnt"])))
        blocks.append(dict(state=canonical_state(state(block["state"], len(ids) + 1)),
            pendingReceipts=list(map(receipt, pending)), outgoingReceipts=list(map(receipt, block["outgoingReceipts"])),
            outcomes=outcomes, tokensBurnt=str(sum(int(row["outcome"]["tokens_burnt"]) for row in block["outcomes"])),
            subsidizedAmount="0", issue=None))
    return blocks


def differences(expected, actual, path=""):
    if type(expected) is not type(actual):
        return [dict(path=path, native=expected, model=actual)]
    if isinstance(expected, dict):
        if expected.keys() != actual.keys():
            return [dict(path=path, nativeKeys=sorted(expected), modelKeys=sorted(actual))]
        return [diff for key in expected for diff in differences(expected[key], actual[key], f"{path}.{key}")]
    if isinstance(expected, list):
        if len(expected) != len(actual):
            return [dict(path=path, nativeLength=len(expected), modelLength=len(actual))]
        return [diff for i, (left, right) in enumerate(zip(expected, actual))
                for diff in differences(left, right, f"{path}[{i}]")]
    return [] if expected == actual else [dict(path=path, native=expected, model=actual)]


def probe(reference, model):
    cases = []
    with frozen_reference(reference) as (native, build), tempfile.TemporaryDirectory(prefix="safe-near-gas-") as directory:
        directory = Path(directory)
        lean = directory / "chain-replay"
        shutil.copy2(model, lean)
        config_dir = directory / "configs"
        config_dir.mkdir()
        configs = {}
        for file in sorted((ROOT / "near-lean/vm/configs").glob("*.json")):
            raw = file.read_bytes()
            (config_dir / file.name).write_bytes(raw)
            configs[file.name] = digest(raw)
        examples = json.loads(subprocess.check_output([str(native), "--financial-examples"], text=True))
        for version in (83, 84, 85, 86):
            for scenario, example in examples.items():
                for purchase, burn in ((0, 0), (10**8, 10**8), (10**8, 2*10**9), (2*10**9, 10**8), (2*10**9, 3*10**9)):
                    source = copy.deepcopy(example)
                    source["protocolVersion"] = version
                    for block in source["blocks"]:
                        block["gasPrice"] = str(purchase)
                    source["blocks"][2]["gasPrice"] = str(burn)
                    native_trace = execute(native, source)
                    if native_trace["stop"] != "blocksExhausted" or native_trace["unrunBlocks"]:
                        raise ValueError("native transfer probe did not execute every block")
                    request = model_request(source, native_trace, config_dir)
                    model_trace = execute(lean, request)
                    expected = dict(formatVersion=1, protocolVersion=version, model="near-lean-chain",
                        initialState=canonical_state(request["initialState"]), initialPendingReceipts=[],
                        blocks=projection(source, native_trace), stop="blocksExhausted", unrunBlocks=0,
                        quiescent=not native_trace["blocks"][-1]["pendingReceipts"], codeCatalogue=[])
                    actual = copy.deepcopy(model_trace)
                    actual["initialState"] = canonical_state(actual["initialState"])
                    for block in actual["blocks"]:
                        block["state"] = canonical_state(block["state"])
                    diffs = differences(expected, actual, "trace")
                    cases.append(dict(scenario=scenario, protocolVersion=version, purchaseBlockPrice=str(purchase), deliveryBlockPrice=str(burn),
                        request=source, modelRequest=request, native=native_trace, model=model_trace, differences=diffs))
        return dict(scope="transfer/account-creation gas regression; not general runtime conformance", build=build,
            leanBinarySha256=hashlib.sha256(lean.read_bytes()).hexdigest(), configSha256=configs,
            unmodeledObservations=["native compute counter", "execution metadata", "account representation version",
                                  "native statistics beyond derived transfer/creation token burn", "trie roots and opaque shard state",
                                  "native hash generation (receipt ids compared under creation-order renaming)",
                                  "transaction hash identity (modeled transaction outcome ids are zero)"],
            cases=cases, differingCases=sum(bool(case["differences"]) for case in cases))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/transfer-gas-regression.json")
    args = parser.parse_args()
    report = probe(args.reference.resolve(), args.model.resolve())
    atomic_write(args.report.resolve(), (json.dumps(report, indent=2) + "\n").encode())
    print(f"Transfer gas regression: {len(report['cases'])} cases, {report['differingCases']} differing cases.")
    print(f"Evidence: {args.report.resolve()}")
    raise SystemExit(bool(report["differingCases"]))


if __name__ == "__main__":
    main()

`just chain-gas-test` runs the targeted native/Lean transfer and account-creation
gas regression after the reference is built. It records all field differences
and explicit observation gaps; it does not establish general runtime conformance.
