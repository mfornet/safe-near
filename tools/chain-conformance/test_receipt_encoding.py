#!/usr/bin/env python3
"""Native ancestry derivation and typed ordinary receipt Borsh comparisons."""
import base64
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

import contract_probe
import import_snapshot as importer
from near_rpc import b58encode
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference
from test_replay import PK, action_receipt, receipt
from trie_probe import REFERENCE, frozen_model

MODEL = ROOT / "near-lean/chain/.lake/build/bin/receipt-encode"
CHAIN = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


def source():
    return dict(formatVersion=1, codes=[], identities=[], receiptIds=[], dataIds=[], receipts=[], actionFormats=[], receivedData=[])


def key_text(pk):
    return ["ed25519:", "secp256k1:"][pk[0]] + b58encode(bytes(pk[1:]))


def native_source(request):
    """Only project original typed values; ancestry stays unresolved in transport."""
    result = copy.deepcopy(request)
    codes = {row["hash"]: Path(row["codePath"]).read_bytes() for row in result.pop("codes")}
    formats = result.pop("actionFormats")
    if len(formats) != len(request["receipts"]): raise ValueError("receipt format count mismatch")
    def permission(value):
        return "FullAccess" if value["kind"] == "fullAccess" else dict(FunctionCall=dict(
            allowance=value["allowance"], receiver_id=value["receiverId"], method_names=value["methodNames"]))
    def access(value): return dict(nonce=value["nonce"], permission=permission(value["permission"]))
    def action(value):
        kind = value["kind"]
        if kind == "createAccount": return dict(CreateAccount={})
        if kind == "deployContract": return dict(DeployContract=dict(code=base64.b64encode(codes[value["codeHash"]]).decode()))
        if kind == "functionCall": return dict(FunctionCall=dict(method_name=value["methodName"],
            args=base64.b64encode(bytes(value["args"])).decode(), gas=value["gas"], deposit=value["deposit"]))
        if kind == "transfer": return dict(Transfer=dict(deposit=value["deposit"]))
        if kind == "stake": return dict(Stake=dict(stake=value["stake"], public_key=key_text(value["publicKey"])))
        if kind == "addKey": return dict(AddKey=dict(public_key=key_text(value["publicKey"]), access_key=access(value["accessKey"])))
        if kind == "deleteKey": return dict(DeleteKey=dict(public_key=key_text(value["publicKey"])))
        if kind == "deleteAccount": return dict(DeleteAccount=dict(beneficiary_id=value["beneficiaryId"]))
        raise ValueError("unknown action")
    rows = []
    for row, format in zip(request["receipts"], formats):
        payload = row["receipt"]
        if payload["kind"] == "data":
            data = payload["data"]
            value = dict(Data=dict(data_id=payload["dataId"], data=None if data is None else base64.b64encode(bytes(data)).decode()))
        else:
            value = dict(Action=dict(signer_id=payload["signerId"], signer_public_key=key_text(payload["signerPublicKey"]),
                gas_price=payload["gasPrice"], output_data_receivers=[dict(data_id=id, receiver_id=receiver)
                    for id, receiver in payload["outputDataReceivers"]], input_data_ids=payload["inputDataIds"],
                actions=[action(value) for value in payload["actions"]]))
            if format == "v2":
                value = dict(ActionV2={**value["Action"], "refund_to": None})
        rows.append(dict(predecessor_id=row["predecessorId"], receiver_id=row["receiverId"], receipt_id=row["receiptId"], receipt=value))
    result["receipts"] = rows
    return result


def graph():
    return [dict(kind="hash", bytes=list(b"original transaction body")),
        dict(kind="transaction", base=0, blockHeight=7), dict(kind="action", base=1, blockHeight=9, index=0),
        dict(kind="data", base=2, blockHeight=9, index=0), dict(kind="receipt", base=1, blockHeight=9, index=0),
        dict(kind="randomSeed", base=2, seed=[255] * 32)]


def cases():
    request = source()
    request["identities"] = graph()
    request["receiptIds"] = [[20, 1], [21, 4]]
    request["dataIds"] = [[40, 3], [41, 5]]
    request["receivedData"] = [None, [], [0, 255, 44]]
    blob = (HERE / "fixtures/replay.wasm").read_bytes()
    name = b58encode(hashlib.sha256(blob).digest())
    request["codes"] = [dict(hash=name, codePath=str(HERE / "fixtures/replay.wasm"), watPath=str(HERE / "fixtures/replay.wat"))]
    for tag, width in [(0, 32), (1, 64)]:
        for allowance in [None, "0", str(2**128 - 1)]:
            value = copy.deepcopy(request)
            key = [tag] + [17] * width
            actions = [dict(kind="createAccount"), dict(kind="deployContract", codeHash=name),
                dict(kind="functionCall", methodName="méthode\0漢字", args=[0, 255], gas=2**64 - 1, deposit=str(2**128 - 1)),
                dict(kind="transfer", deposit="0"), dict(kind="stake", stake=str(2**128 - 1), publicKey=key),
                dict(kind="addKey", publicKey=key, accessKey=dict(nonce=2**64 - 1, permission=dict(kind="functionCall",
                    allowance=allowance, receiverId="not an account\0🦀", methodNames=["", "x", "x", "\0漢字"]))),
                dict(kind="deleteKey", publicKey=key), dict(kind="deleteAccount", beneficiaryId="a" * 64)]
            action = action_receipt(actions)
            action["receipt"].update(signerPublicKey=key, gasPrice=str(2**128 - 1))
            value["receipts"] = [action] + [receipt(dict(kind="data", dataId=40, data=data), 21) for data in [None, [], [0, 255]]]
            value["actionFormats"] = ["legacy"] * 4
            yield f"all-actions-{tag}-{allowance}", value
            value = copy.deepcopy(value)
            value["actionFormats"][0] = "v2"
            yield f"all-actions-v2-{tag}-{allowance}", value
    rng = random.Random(671901)
    for index in range(40):
        value = copy.deepcopy(request)
        actions = []
        for _ in range(rng.randrange(12)):
            key = [0] + list(rng.randbytes(32))
            actions.append(rng.choice([dict(kind="transfer", deposit=str(rng.getrandbits(128))),
                dict(kind="functionCall", methodName="call", args=list(rng.randbytes(rng.randrange(60))),
                    gas=rng.getrandbits(64), deposit=str(rng.getrandbits(128))),
                dict(kind="addKey", publicKey=key, accessKey=dict(nonce=rng.getrandbits(64), permission=dict(kind="fullAccess")))]))
        value["receipts"] = [action_receipt(actions), receipt(dict(kind="data", dataId=40, data=list(rng.randbytes(rng.randrange(60)))), 21)]
        value["actionFormats"] = [rng.choice(["legacy", "v2"]), "legacy"]
        yield f"random-receipts-{index}", value
    value = source()
    for message in [b"", b"abc"] + [rng.randbytes(n) for n in range(130)]:
        base = len(value["identities"])
        value["identities"].append(dict(kind="hash", bytes=list(message)))
        for height in [0, 1, 2**32, 2**64 - 1]:
            value["identities"].append(dict(kind="transaction", base=base, blockHeight=height))
            for kind in ["receipt", "action", "data"]:
                for offset in [0, 1, 2**32, 2**64 - 1]:
                    value["identities"].append(dict(kind=kind, base=base, blockHeight=height, index=offset))
        value["identities"].append(dict(kind="randomSeed", base=base, seed=list(rng.randbytes(32))))
    yield "identity-boundaries", value
    value = source()
    value["identities"] = [dict(kind="input", hash=blob) for blob in [[0] * 32, [255] * 32, list(range(32))]] + [
        dict(kind="receipt", base=index, blockHeight=2**64 - 1, index=2**64 - 1) for index in range(3)]
    yield "explicit-initial-identities", value


class ReceiptEncodingTests(unittest.TestCase):
    def setUp(self): self.evidence = []

    def test_all_actions_permissions_payloads_and_ancestry(self):
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum):
            for name, request in cases():
                with self.subTest(scenario=name):
                    projected = native_source(request)
                    expected = importer.native_call(native, "--encode-receipts", projected)
                    actual = importer.execute(model, request, ROOT)
                    self.evidence.append(dict(scenario=name, request=request, nativeRequest=projected, native=expected, model=actual))
                    self.assertEqual(actual, expected)
                    if request["receivedData"]:
                        self.assertEqual(actual["receivedData"][:2], [[0], [1, 0, 0, 0, 0]])
        atomic_write(ROOT / "audit/receipt-encoding-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, runtimeIntegrated=False, cases=self.evidence), indent=2) + "\n").encode())

    def test_original_signed_transactions_derive_actual_runtime_callback_ids(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for method in ["spawn", "spawn_fail", "spawn_twice"]:
                    target = Path(directory) / f"{protocol}-{method}"
                    scenario = contract_probe.scenario("spawn" if method == "spawn_twice" else method, "all")
                    count = 2 if method == "spawn_twice" else 1
                    if count == 2:
                        transaction = scenario["blocks"][0]["transactions"][0]
                        transaction["actions"] = [copy.deepcopy(transaction["actions"][0]) for _ in range(count)]
                        for action in transaction["actions"]: action["FunctionCall"]["gas"] = 120 * 10**12
                    importer.prepare(contract_probe.snapshot(protocol), target, reference=REFERENCE, model=CHAIN,
                        scenario=scenario)
                    original = json.loads((target / "native.json").read_text())
                    trace = importer.execute(native, original, target)
                    signed = original["blocks"][0]["transactions"][0]
                    # The caller is explicitly Ed25519: its trailing signature is tag 0 + 64 bytes.
                    self.assertEqual(signed[-65], 0)
                    request = source()
                    request["identities"] = [dict(kind="hash", bytes=signed[:-65]), dict(kind="transaction", base=0, blockHeight=101)]
                    for action in range(count):
                        position = len(request["identities"])
                        request["identities"] += [dict(kind="action", base=1, blockHeight=102, index=action),
                            dict(kind="data", base=position, blockHeight=102, index=0)]
                    start = len(request["identities"])
                    request["identities"] += [dict(kind="receipt", base=1, blockHeight=102, index=index) for index in range(2 * count + 1)]
                    actual = importer.execute(model, request, ROOT)
                    hashes = [b58encode(bytes(value)) for value in actual["hashes"]]
                    self.assertEqual(hashes[0], trace["blocks"][0]["inputs"]["transactions"][0]["view"]["hash"])
                    self.assertEqual(hashes[1], trace["blocks"][0]["outgoingReceipts"][0]["receipt_id"])
                    children = trace["blocks"][1]["outgoingReceipts"]
                    self.assertEqual(hashes[start:], [row["receipt_id"] for row in children])
                    for action in range(count):
                        data_id = hashes[3 + 2 * action]
                        self.assertEqual(data_id, children[2 * action]["receipt"]["ActionV2"]["output_data_receivers"][0]["data_id"])
                        self.assertEqual([data_id], children[2 * action + 1]["receipt"]["ActionV2"]["input_data_ids"])
                    evidence.append(dict(protocol=protocol, method=method, originalRequest=original,
                        trace=trace, modelRequest=request, model=actual))
        atomic_write(ROOT / "audit/runtime-identity-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, runtimeIntegrated=False, cases=evidence), indent=2) + "\n").encode())

    def test_invalid_ancestry_missing_alias_and_duplicate_bindings_fail_closed(self):
        variants = []
        for operation in [dict(kind="unknown"), dict(kind="input", hash=[0] * 31), dict(kind="hash", bytes=[256]),
                dict(kind="receipt", base=0, blockHeight=0, index=0), dict(kind="transaction", base=False, blockHeight=0)]:
            value = source(); value["identities"] = [operation]; variants.append(value)
        for field, number in [("blockHeight", 2**64), ("index", 2**64), ("index", -1), ("base", 100)]:
            value = source(); value["identities"] = graph()
            value["identities"][2][field] = number; variants.append(value)
        for ids in [[[20, 1], [20, 4]], [[20, 1], [21, 1]], [[20, 100]]]:
            value = source(); value["identities"] = graph(); value["receiptIds"] = ids; variants.append(value)
        value = source(); value["receipts"] = [action_receipt([])]; variants.append(value)
        value = source(); value["identities"] = graph(); value["receiptIds"] = [[20, 1]]
        value["receipts"] = [receipt(dict(kind="data", dataId=40, data=None))]; variants.append(value)
        for value in variants:
            value["actionFormats"] = ["legacy"] * len(value["receipts"])
            with self.subTest(request=value), frozen_reference(REFERENCE) as (native, _), frozen_model(MODEL) as (model, _):
                with self.assertRaises(subprocess.CalledProcessError): importer.native_call(native, "--encode-receipts", native_source(value))
                result = subprocess.run([str(model)], input=json.dumps(value), text=True, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertTrue(result.stderr)


if __name__ == "__main__":
    unittest.main()
