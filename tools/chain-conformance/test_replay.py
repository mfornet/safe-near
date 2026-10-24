#!/usr/bin/env python3
"""Exercise the real Lean chain JSON executable; no native-equivalence claim."""

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"
FIXTURE = ROOT / "tools/chain-conformance/fixtures/replay"
ONE = 10 ** 24
PK = [0] + [1] * 32


def account(amount, code=None):
    return {"amount": str(amount), "locked": "0", "codeHash": code, "global": None,
            "versionTwo": False, "storageUsage": 182}


def empty_state():
    return {"accounts": [["alice.near", account(100 * ONE)], ["bob.near", account(10 * ONE)]],
            "accessKeys": [[["alice.near", PK], {"nonce": 0, "permission": {"kind": "fullAccess"}}]],
            "storage": [], "postponed": [], "pendingDataCount": [], "postponedByData": [],
            "receivedData": [], "delayed": [], "nextId": 1, "globalCode": [], "globalNonces": [],
            "gasKeyNonces": [], "yieldIndices": None, "yieldTimeouts": [], "yieldReceipts": [],
            "yieldStatus": []}


def block(transactions=(), incoming=None, height=7):
    return {"blockHeight": height, "blockTimestamp": height * 10 ** 9, "epochHeight": 0,
            "gasPrice": "100000000", "gasLimit": None, "randomSeed": [0] * 32,
            "transactions": list(transactions), "incomingIndices": incoming}


def tx(actions, receiver="bob.near", nonce=1):
    return {"signerId": "alice.near", "publicKey": PK, "nonce": nonce,
            "receiverId": receiver, "actions": actions}


def transfer(amount=ONE):
    return {"kind": "transfer", "deposit": str(amount)}


def call(method):
    return {"kind": "functionCall", "methodName": method, "args": [], "gas": 10 ** 14, "deposit": "0"}


def receipt(payload, identifier=20):
    return {"predecessorId": "alice.near", "receiverId": "bob.near", "receiptId": identifier,
            "receipt": payload}


def action_receipt(actions, identifier=20):
    return receipt({"kind": "action", "signerId": "alice.near", "signerPublicKey": PK,
                    "gasPrice": "100000000", "outputDataReceivers": [[41, "alice.near"]],
                    "inputDataIds": [40], "actions": actions, "yieldDataId": None}, identifier)


def request():
    return {"formatVersion": 1, "protocolVersion": 86, "configDir": str(ROOT / "near-lean/vm/configs"),
            "codes": [], "initialState": empty_state(), "pendingReceipts": [], "blocks": []}


def execute(value):
    process = subprocess.run([str(BINARY)], input=json.dumps(value), text=True, capture_output=True)
    if process.returncode:
        raise AssertionError(process.stderr)
    return json.loads(process.stdout)


def accounts(state):
    return dict(state["accounts"])


class ChainReplayTests(unittest.TestCase):
    def catalogue(self, value, directory):
        value["codes"] = [{"hash": "replay", "codePath": str(FIXTURE.with_suffix(".wasm")),
                           "watPath": str(FIXTURE.with_suffix(".wat"))}]
        empty_wasm, empty_wat = Path(directory) / "empty.wasm", Path(directory) / "empty.wat"
        empty_wasm.write_bytes(b"\0asm\1\0\0\0")
        empty_wat.write_text("(module)")
        value["codes"].append({"hash": "empty", "codePath": str(empty_wasm), "watPath": str(empty_wat)})

    def test_transaction_envelope_rejects_bad_tags_modes_and_gas_key_lanes(self):
        for patch in [{"version": 2}, {"version": True}, {"version": None},
                      {"version": 1, "nonceMode": "Strict"}, {"version": 0, "nonceMode": "strict"},
                      {"version": 1, "nonceMode": None}, {"version": 1, "nonceIndex": 0}]:
            with self.subTest(patch=patch):
                value = request()
                transaction = tx([transfer()])
                transaction.update(patch)
                value["blocks"] = [block([transaction])]
                result = subprocess.run([str(BINARY)], input=json.dumps(value), text=True, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertTrue(result.stderr)

    def test_transfer_frontiers_idle_blocks_and_complete_state_continuation(self):
        value = request()
        value["blocks"] = [block([tx([transfer()])]), block(incoming=[], height=8),
                           block(height=9), block(height=10),
                           block([tx([transfer()], receiver="alice.near", nonce=2)], height=11),
                           block(height=12)]
        trace = execute(value)
        self.assertEqual(trace["stop"], "blocksExhausted")
        self.assertEqual(trace["unrunBlocks"], 0)
        self.assertTrue(trace["quiescent"])
        blocks = trace["blocks"]
        self.assertEqual(len(blocks[0]["outcomes"]), 1)
        self.assertEqual(accounts(blocks[0]["state"])["bob.near"]["amount"], str(10 * ONE))
        self.assertEqual(blocks[1]["state"], blocks[0]["state"])
        self.assertEqual(blocks[1]["pendingReceipts"], blocks[0]["pendingReceipts"])
        self.assertEqual(accounts(blocks[2]["state"])["bob.near"]["amount"], str(11 * ONE))
        self.assertEqual(len(blocks[4]["outcomes"]), 2)
        total = sum(int(a["amount"]) + int(a["locked"]) for a in accounts(blocks[-1]["state"]).values())
        self.assertEqual(total + sum(int(b["tokensBurnt"]) for b in blocks), 110 * ONE)
        resumed = copy.deepcopy(value)
        resumed["initialState"] = blocks[0]["state"]
        resumed["pendingReceipts"] = blocks[0]["pendingReceipts"]
        resumed["blocks"] = value["blocks"][1:]
        self.assertEqual(execute(resumed)["blocks"], blocks[1:])

    def test_invalid_schedule_is_atomic_and_stops_the_sequence(self):
        for positions in ([0, 0], [2]):
            with self.subTest(positions=positions):
                value = request()
                value["blocks"] = [block([tx([transfer()])]),
                                   block([tx([transfer()], nonce=2)], incoming=positions), block()]
                result = execute(value)
                self.assertEqual(result["stop"], "invalidSchedule")
                self.assertEqual(result["unrunBlocks"], 1)
                self.assertEqual(result["blocks"][1]["state"], result["blocks"][0]["state"])
                self.assertEqual(result["blocks"][1]["pendingReceipts"], result["blocks"][0]["pendingReceipts"])
                self.assertEqual(result["blocks"][1]["scheduleError"]["kind"], "unavailableIndex")

    def test_every_state_and_receipt_field_survives_serialization(self):
        with tempfile.TemporaryDirectory() as directory:
            value = request()
            self.catalogue(value, directory)
            actions = [{"kind": "createAccount"}, {"kind": "deployContract", "codeHash": "replay"},
                       call("ping"), transfer(), {"kind": "stake", "stake": "4", "publicKey": PK},
                       {"kind": "addKey", "publicKey": PK, "accessKey": {"nonce": 9, "permission": {
                           "kind": "functionCall", "allowance": "123", "receiverId": "bob.near", "methodNames": ["x"]}}},
                       {"kind": "deleteKey", "publicKey": PK}, {"kind": "deleteAccount", "beneficiaryId": "alice.near"}]
            action = action_receipt(actions)
            failed = receipt({"kind": "data", "dataId": 43, "data": None, "resumeDataId": None}, 22)
            empty = receipt({"kind": "data", "dataId": 44, "data": [], "resumeDataId": None}, 23)
            state = value["initialState"]
            state["accounts"][0][1].update(codeHash="replay", locked="345")
            state["accessKeys"].append([["bob.near", [0] + [2] * 32], {"nonce": 8, "permission": {
                "kind": "functionCall", "allowance": None, "receiverId": "alice.near", "methodNames": []}}])
            state.update(storage=[["alice.near", [[[0, 255], [255, 0]], [[], []]]]],
                         postponed=[[20, action]], pendingDataCount=[[20, 1]], postponedByData=[[40, 20]],
                         receivedData=[[41, None], [42, []], [45, [0, 255]]], delayed=[failed, empty], nextId=50)
            value["pendingReceipts"] = [action, failed, empty]
            result = execute(value)
            self.assertEqual(result["initialState"], state)
            self.assertEqual(result["initialPendingReceipts"], value["pendingReceipts"])
            self.assertFalse(result["quiescent"])
            self.assertEqual(result["blocks"], [])

    def test_create_deploy_call_keys_and_delete_execute_through_the_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            value = request()
            self.catalogue(value, directory)
            actions = [{"kind": "createAccount"}, transfer(),
                       {"kind": "deployContract", "codeHash": "replay"},
                       {"kind": "addKey", "publicKey": PK, "accessKey": {"nonce": 0, "permission": {"kind": "fullAccess"}}},
                       call("ping"), {"kind": "deleteKey", "publicKey": PK},
                       {"kind": "deleteAccount", "beneficiaryId": "alice.near"}]
            value["blocks"] = [block([tx(actions, receiver="child.alice.near")])] + [block(height=h) for h in range(8, 13)]
            result = execute(value)
            self.assertTrue(result["quiescent"])
            self.assertTrue(all(b["issue"] is None for b in result["blocks"]))
            self.assertEqual(result["blocks"][1]["outcomes"][0]["outcome"]["status"]["kind"], "successValue")
            self.assertNotIn("child.alice.near", accounts(result["blocks"][-1]["state"]))
            self.assertFalse(any(owner == "child.alice.near" for (owner, _), _ in result["blocks"][-1]["state"]["accessKeys"]))

    def test_emitted_deployment_uses_the_catalogue_or_rejects_atomically(self):
        with tempfile.TemporaryDirectory() as directory:
            value = request()
            self.catalogue(value, directory)
            value["initialState"]["accounts"][0][1]["codeHash"] = "replay"
            value["blocks"] = [block([tx([call("deploy")], receiver="alice.near")]), block(height=8), block(height=9)]
            known = execute(value)
            self.assertTrue(all(b["issue"] is None for b in known["blocks"]))
            self.assertEqual(accounts(known["blocks"][1]["state"])["alice.near"]["codeHash"], "empty")
            value["codes"] = value["codes"][:1]
            missing = execute(value)
            self.assertEqual(missing["stop"], "executionIssue")
            self.assertEqual(missing["unrunBlocks"], 2)
            self.assertEqual(missing["blocks"][0]["state"], value["initialState"])
            self.assertEqual(missing["blocks"][0]["outcomes"], [])
            self.assertEqual(missing["blocks"][0]["outgoingReceipts"], [])
            self.assertEqual(missing["blocks"][0]["tokensBurnt"], "0")
            self.assertIn("catalogue", missing["blocks"][0]["issue"]["message"])

    def test_unknown_signature_encoding_is_a_model_issue_without_charging(self):
        for earlier in [[], [tx([transfer()])]]:
            with self.subTest(earlier=bool(earlier)):
                value = request()
                transaction = tx([transfer()], nonce=2 if earlier else 1)
                transaction["publicKey"] = [2] + [0] * 32
                value["blocks"] = [block(earlier + [transaction])]
                result = execute(value)
                self.assertEqual(result["stop"], "executionIssue")
                self.assertEqual(result["blocks"][0]["state"], value["initialState"])
                self.assertEqual(result["blocks"][0]["tokensBurnt"], "0")
                self.assertEqual(result["blocks"][0]["outcomes"], [])
                self.assertEqual(result["blocks"][0]["outgoingReceipts"], [])
                self.assertIsNone(result["blocks"][0]["transactionSizes"][-1]["wireSize"])
                self.assertIn("signature/key encoding", result["blocks"][0]["issue"]["message"])

    def test_malformed_inputs_fail_without_a_trace(self):
        changes = [
            lambda v: v.update(extra=True), lambda v: v.pop("blocks"),
            lambda v: v.update(formatVersion=2), lambda v: v.update(protocolVersion=87),
            lambda v: v["initialState"].update(extra=True),
            lambda v: v["initialState"]["accounts"].append(v["initialState"]["accounts"][0]),
            lambda v: v["initialState"]["accessKeys"].append(v["initialState"]["accessKeys"][0]),
            lambda v: v["initialState"].update(storage=[["alice.near", [[[0], []], [[0], [1]]]]]),
            lambda v: v["initialState"].update(storage=[["alice.near", [[[256], []]]]]),
            lambda v: v["initialState"]["accounts"][0][1].update(amount="-1"),
            lambda v: v["initialState"]["accounts"][0][1].update(amount=str(2 ** 128)),
            lambda v: v["initialState"]["accounts"][0][1].update(storageUsage=2 ** 64),
            lambda v: v["initialState"]["accounts"][0][1].update(codeHash="unknown"),
            lambda v: v["initialState"]["accessKeys"][0][1].update(permission={"kind": "unknown"}),
            lambda v: v["blocks"][0].update(blockHeight=2 ** 64),
            lambda v: v["blocks"][0].update(randomSeed=[0] * 31),
            lambda v: v["blocks"][0].update(gasLimit=2 ** 64),
            lambda v: v["blocks"][0].update(gasPrice="1e3"),
            lambda v: v["blocks"][0].update(incomingIndices=[-1]),
            lambda v: v["blocks"][0]["transactions"][0].update(nonce=2 ** 64),
            lambda v: v["blocks"][0]["transactions"][0].update(publicKey=[-1]),
            lambda v: v["blocks"][0]["transactions"][0].update(actions=[{"kind": "unknown"}]),
            lambda v: v.update(pendingReceipts=[receipt({"kind": "unknown"})]),
            lambda v: v["initialState"].update(postponed=[[21, action_receipt([])]]),
        ]
        for index, change in enumerate(changes):
            with self.subTest(index=index):
                value = request()
                value["blocks"] = [block([tx([transfer()])])]
                change(value)
                process = subprocess.run([str(BINARY)], input=json.dumps(value), text=True, capture_output=True)
                self.assertNotEqual(process.returncode, 0)
                self.assertEqual(process.stdout.strip(), "")
        # Parse every supplied block before starting the first one.
        value = request()
        value["blocks"] = [block([tx([transfer()])]), {"invalid": True}]
        process = subprocess.run([str(BINARY)], input=json.dumps(value), text=True, capture_output=True)
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(process.stdout.strip(), "")

    def test_catalogue_errors_fail_without_an_executable_placeholder(self):
        with tempfile.TemporaryDirectory() as directory:
            value = request()
            self.catalogue(value, directory)
            for code in (dict(value["codes"][0]), {**value["codes"][0], "hash": "other"}):
                duplicate = copy.deepcopy(value)
                duplicate["codes"].append(code)
                process = subprocess.run([str(BINARY)], input=json.dumps(duplicate), text=True, capture_output=True)
                self.assertNotEqual(process.returncode, 0)
                self.assertIn("duplicate catalogue", process.stderr)
                self.assertEqual(process.stdout.strip(), "")
            bad = Path(directory) / "invalid.wasm"
            bad.write_bytes(b"\x00asm\x01\x00\x00\x00\x01")
            value["codes"][0]["codePath"] = str(bad)
            process = subprocess.run([str(BINARY)], input=json.dumps(value), text=True, capture_output=True)
            self.assertNotEqual(process.returncode, 0)
            self.assertEqual(process.stdout.strip(), "")

    def test_stdin_is_one_complete_json_document(self):
        process = subprocess.run([str(BINARY)], input=json.dumps(request(), indent=2), text=True, capture_output=True)
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout)["stop"], "blocksExhausted")
        process = subprocess.run([str(BINARY)], input=json.dumps(request()) + "\n{}", text=True, capture_output=True)
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(process.stdout.strip(), "")


if __name__ == "__main__":
    unittest.main()
