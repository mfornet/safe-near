#!/usr/bin/env python3
"""Native/Lean integration for captured-state import; no RPC requests."""

import base64
import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import import_snapshot as importer
from prepare import HERE, ROOT
from probe import execute, frozen_reference
from near_rpc import b58encode

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


def snapshot():
    blob = (HERE / "fixtures/replay.wasm").read_bytes()
    config = json.loads((ROOT / "near-lean/vm/configs/runtime_config_v86.json").read_text())
    return dict(format="safe-near-snapshot-v1", block=dict(header=dict(hash="1" * 32, height=100)),
        protocol_config=dict(protocol_version=86, runtime_config={k: v for k, v in config.items() if k not in {"runtime_finance", "runtime_admission"}}),
        scope=dict(all_accounts=False, receipt_queues=False, state_proofs_verified=False),
        accounts=[dict(account_id="captured.near", account=dict(amount=str(10 * 10**24), locked="17",
            code_hash=importer.code_hash(blob), storage_usage=400, storage_paid_at=0),
            code=dict(hash=importer.code_hash(blob), code_base64=base64.b64encode(blob).decode()),
            access_keys=[dict(public_key="ed25519:" + "1" * 32, access_key=dict(nonce=8, permission="FullAccess")),
                dict(public_key="ed25519:" + b58encode(bytes([1]) * 32), access_key=dict(nonce=9, permission={"FunctionCall": {
                    "allowance": "123456", "receiver_id": "other.near", "method_names": ["alpha", "beta"]}}))],
            gas_key_nonces=[], storage=dict(complete=True, prefixes_base64=[""], values=[
                dict(key=base64.b64encode(key).decode(), value=base64.b64encode(value).decode())
                for key, value in [(b"", b"\0\xff"), (b"STATE", b"payload"), (b"x\xff", b"")]]))])


def block(height, transactions=(), indices=None):
    return dict(blockHeight=height, blockTimestamp=height * 10**9, epochHeight=0,
        gasPrice="100000000", gasLimit=None, randomSeed=[0] * 32, prevBlockHash=[0] * 32,
        incomingIndices=indices, transactions=list(transactions))


def scenario():
    tx = dict(receiverId="captured.near", nonce=1, actions=[{"FunctionCall": {
        "method_name": "ping", "args": "", "gas": 50 * 10**12, "deposit": "0"}}])
    return dict(caller=dict(accountId="fixture-caller.near", seed="safe-near-import-test", amount=str(100 * 10**24)),
                blocks=[block(101, [tx]), block(102, indices=[]), block(103), block(104)])


class SnapshotImportTests(unittest.TestCase):
    def test_complete_state_import_and_portable_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "fixture"
            original = snapshot()
            manifest = importer.prepare(original, target, reference=REFERENCE, model=MODEL)
            self.assertTrue(manifest["genesisProjectionMatches"])
            self.assertFalse(manifest["executionComparisonEstablished"])
            self.assertFalse(manifest["historicalReplayEstablished"])
            self.assertTrue(manifest["capturedRpcConfigMatchesPinnedView"])
            self.assertTrue(manifest["scope"]["queuesExplicitlyEmpty"])
            self.assertFalse(manifest["scope"]["stateProofsVerified"])
            for name, expected in manifest["files"].items():
                self.assertEqual(importer.file_digest(target / name), expected)
            model = json.loads((target / "model.json").read_text())
            state = model["initialState"]
            self.assertEqual(state["accounts"][0][1]["locked"], "17")
            self.assertEqual(len(state["accessKeys"]), 2)
            self.assertEqual(state["storage"][0][1], [[[], [0, 255]], [list(b"STATE"), list(b"payload")], [list(b"x\xff"), []]])
            moved = Path(directory) / "relocated"
            shutil.copytree(target, moved)
            result = importer.execute(MODEL, model, moved)
            self.assertEqual(result["initialState"], state)
            self.assertEqual(result["blocks"], [])
            with self.assertRaises(FileExistsError):
                importer.prepare(original, target, reference=REFERENCE, model=MODEL)

    def test_native_signing_and_real_contract_calls(self):
        with tempfile.TemporaryDirectory() as directory, frozen_reference(REFERENCE) as (native, _):
            target = Path(directory) / "fixture"
            importer.prepare(snapshot(), target, reference=REFERENCE, model=MODEL, scenario=scenario())
            source = json.loads((target / "native.json").read_text())
            model = json.loads((target / "model.json").read_text())
            left = execute(native, source)
            right = importer.execute(MODEL, model, target)
            self.assertEqual(left["stop"], "blocksExhausted")
            self.assertEqual(right["stop"], "blocksExhausted")
            self.assertEqual(left["unrunBlocks"], 0)
            self.assertEqual(right["unrunBlocks"], 0)
            self.assertEqual(len(left["blocks"][0]["outcomes"]), 1)
            self.assertEqual(len(right["blocks"][0]["outcomes"]), 1)
            self.assertEqual(left["blocks"][1]["outcomes"], [])
            self.assertEqual(right["blocks"][1]["outcomes"], [])
            native_call = left["blocks"][2]["outcomes"][0]["outcome"]
            model_call = right["blocks"][2]["outcomes"][0]["outcome"]
            self.assertEqual(native_call["status"], {"SuccessValue": ""})
            self.assertEqual(model_call["status"], {"kind": "successValue", "value": []})
            self.assertTrue(right["quiescent"])
            self.assertEqual(left["blocks"][-1]["pendingReceipts"], [])
            for b in right["blocks"]:
                self.assertIsNone(b["issue"])

    def test_all_eight_action_encodings_bind_native_transaction_views(self):
        with frozen_reference(REFERENCE) as (native, _):
            key = "ed25519:" + "1" * 32
            raw = [{"CreateAccount": {}}, {"DeployContract": {"code": "AGFzbQEAAAA="}},
                {"FunctionCall": {"method_name": "ping", "args": "AP8=", "gas": 123, "deposit": "4"}},
                {"Transfer": {"deposit": "5"}}, {"Stake": {"stake": "6", "public_key": key}},
                {"AddKey": {"public_key": key, "access_key": {"nonce": 7, "permission": "FullAccess"}}},
                {"DeleteKey": {"public_key": key}}, {"DeleteAccount": {"beneficiary_id": "beneficiary.near"}}]
            request = dict(signerId="fixture-caller.near", seed="safe-near-import-test", transactions=[dict(
                receiverId="captured.near", nonce=1, blockHash=[0] * 32, actions=raw)])
            one = importer.native_call(native, "--sign-transactions", request)
            self.assertEqual(one, importer.native_call(native, "--sign-transactions", request))
            self.assertEqual(one["transactions"][0]["actions"], raw)
            codes = {}
            converted = [importer.action(value, one["actionPublicKeys"], codes) for value in one["transactions"][0]["actions"]]
            self.assertEqual([value["kind"] for value in converted], ["createAccount", "deployContract", "functionCall",
                "transfer", "stake", "addKey", "deleteKey", "deleteAccount"])
            self.assertEqual(converted[2]["args"], [0, 255])
            self.assertEqual(converted[5]["accessKey"]["nonce"], 7)
            self.assertEqual(len(codes), 1)
            self.assertEqual(next(iter(codes.values())), b"\0asm\1\0\0\0")
            self.assertNotEqual(one["transactions"][0]["view"]["actions"][1]["DeployContract"]["code"],
                one["transactions"][0]["actions"][1]["DeployContract"]["code"])
            request["transactions"][0]["actions"][2]["FunctionCall"]["ignored"] = 1
            with self.assertRaises(subprocess.CalledProcessError):
                importer.native_call(native, "--sign-transactions", request)

    def test_synthetic_callers_cannot_replace_capture_or_protocol_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            for identifier in ["captured.near", "system"]:
                request = scenario()
                request["caller"]["accountId"] = identifier
                with self.subTest(identifier=identifier), self.assertRaises(ValueError):
                    importer.prepare(snapshot(), Path(directory) / "fixture", reference=REFERENCE, model=MODEL, scenario=request)
            request = scenario()
            del request["caller"]
            with self.assertRaises(ValueError):
                importer.prepare(snapshot(), Path(directory) / "fixture", reference=REFERENCE, model=MODEL, scenario=request)

    def test_synthetic_key_overrides_reject_unrepresented_fields_and_numeric_overflow(self):
        invalid = [dict(nonce=2**64, permission="FullAccess"),
            dict(nonce=0, permission="FullAccess", unknown=1),
            dict(nonce=0, permission={"FunctionCall": {"allowance": str(2**128),
                "receiver_id": "captured.near", "method_names": ["ping"]}}),
            dict(nonce=0, permission={"FunctionCall": {"allowance": None,
                "receiver_id": "captured.near", "method_names": [7]}})]
        with tempfile.TemporaryDirectory() as directory:
            for index, key in enumerate(invalid):
                with self.subTest(key=key):
                    request = scenario()
                    request["caller"]["accessKey"] = key
                    target = Path(directory) / str(index)
                    with self.assertRaises(ValueError):
                        importer.prepare(snapshot(), target, reference=REFERENCE, model=MODEL, scenario=request)
                    self.assertFalse(target.exists())

    def test_native_encoder_rejects_duplicates_and_unknown_access_key_fields(self):
        with frozen_reference(REFERENCE) as (native, _):
            rows, _, _ = importer.validate_snapshot(snapshot())
            first = importer.native_call(native, "--encode-state", {"accounts": rows})
            self.assertEqual(first, importer.native_call(native, "--encode-state", {"accounts": rows}))
            for change in (lambda x: x.append(x[0]),
                           lambda x: x[0]["storage"].append(x[0]["storage"][0]),
                           lambda x: x[0]["keys"][0]["accessKey"].update(ignored=True)):
                with self.subTest(change=change):
                    bad = copy.deepcopy(rows)
                    change(bad)
                    with self.assertRaises(subprocess.CalledProcessError):
                        importer.native_call(native, "--encode-state", {"accounts": bad})


if __name__ == "__main__":
    unittest.main()
