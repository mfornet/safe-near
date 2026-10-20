#!/usr/bin/env python3
"""Original typed bodies -> native transaction hashes and admitted receipt IDs."""
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

import compare_fixture as comparator
import contract_probe
import import_snapshot as importer
from gas_probe import canonical_state
from near_rpc import b58encode
from prepare import ROOT, atomic_write
from probe import frozen_reference
from test_receipt_encoding import CHAIN, cases as receipt_cases, native_source as receipt_source, source as receipt_request
from test_replay import PK, action_receipt, empty_state, tx, transfer
from test_state_encoding import MODEL as STATE, entries
from trie_probe import REFERENCE, frozen_model

MODEL = ROOT / "near-lean/chain/.lake/build/bin/transaction-replay"


def project_actions(actions, codes):
    value = receipt_request()
    value.update(codes=codes, receipts=[action_receipt(actions)], actionFormats=["legacy"])
    return receipt_source(value)["receipts"][0]["receipt"]["Action"]["actions"]


def codec_cases():
    rng = random.Random(492186)
    _, fixture = next(receipt_cases())
    actions = fixture["receipts"][0]["receipt"]["actions"]
    lists = [[], actions] + [[action] for action in actions]
    lists += [[dict(kind="addKey", publicKey=PK, accessKey=dict(nonce=2**64 - 1,
        permission=dict(kind="functionCall", allowance=allowance, receiverId="not an account\0漢字", methodNames=["", "é", "x", "x"])))]
        for allowance in [None, "0", str(2**128 - 1)]]
    lists += [[dict(kind="functionCall", methodName="méthode\0", args=list(rng.randbytes(index)),
        gas=rng.getrandbits(64), deposit=str(rng.getrandbits(128)))] for index in range(48)]
    for key in ["ed25519", "secp256k1"]:
        for version, mode in [(0, "monotonic"), (1, "monotonic"), (1, "strict")]:
            rows = [dict(version=version, nonceMode=mode, receiverId="receiver.near" if index % 2 else "a" * 64,
                nonce=2**64 - 1 if index == 0 else rng.getrandbits(64), blockHash=list(rng.randbytes(32)),
                actions=project_actions(actions, fixture["codes"])) for index, actions in enumerate(lists)]
            yield key, version, mode, fixture["codes"], lists, rows


def source():
    return dict(formatVersion=1, codes=[], transactions=[dict(transaction=tx([transfer()]), blockHash=[0] * 32)])


class TransactionEncodingTests(unittest.TestCase):
    def test_native_bodies_hashes_all_actions_envelopes_keys_and_block_hashes(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum):
            for key, version, mode, codes, actions, rows in codec_cases():
                signing = dict(signerId="caller.near", seed="original-body-fixture", keyType=key, transactions=rows)
                signed = importer.native_call(native, "--sign-transactions", signing)
                request = dict(formatVersion=1, codes=codes, transactions=[dict(blockHash=row["blockHash"], transaction=dict(
                    version=version, signerId=signing["signerId"], publicKey=signed["publicKeyBorsh"], nonce=row["nonce"],
                    nonceMode=mode, receiverId=row["receiverId"], actions=actions[index])) for index, row in enumerate(rows)])
                actual = importer.execute(model, request, ROOT)
                self.assertIsNone(actual["registry"])
                self.assertEqual(len(actual["transactions"]), len(rows))
                for expected, encoded in zip(signed["transactions"], actual["transactions"]):
                    signature = 65 if key == "ed25519" else 66
                    body = expected["borsh"][:-signature]
                    self.assertEqual(set(encoded), {"body", "bodySize", "hash"})
                    self.assertEqual(encoded["body"], body)
                    self.assertEqual(encoded["bodySize"], expected["bodySize"])
                    self.assertEqual(encoded["hash"], list(hashlib.sha256(bytes(body)).digest()))
                    self.assertEqual(b58encode(bytes(encoded["hash"])), expected["view"]["hash"])
                evidence.append(dict(keyType=key, version=version, nonceMode=mode, signingRequest=signing, native=signed, request=request, model=actual))
        atomic_write(ROOT / "audit/transaction-encoding-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, signedBodyEncoding=True, runtimeReceiptRegistration=False, cases=evidence), indent=2) + "\n").encode())

    def test_automatic_receipt_registration_matches_native_admitted_prefixes(self):
        evidence = []
        vectors = [(0, "monotonic", 1), (1, "strict", 2), (1, "strict", 4), (1, "monotonic", 9),
            (1, "strict", 10), (0, "monotonic", 11), (0, "monotonic", 11), (0, "monotonic", 12)]
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum), frozen_model(STATE) as (state_model, state_checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for key in ["ed25519", "secp256k1"]:
                    for policy in ["full", "restricted", "poor"]:
                        with self.subTest(protocol=protocol, key=key, policy=policy):
                            height = {"full": 101, "restricted": 1, "poor": 65537}[policy]
                            price = {"full": "100000000", "restricted": "1000000000", "poor": "0"}[policy]
                            caller = dict(accountId="fixture-caller.near", seed="automatic-tx-registry", keyType=key,
                                amount=str((0 if policy == "poor" else 100) * 10**24))
                            if policy == "restricted": caller["accessKey"] = dict(nonce=0, permission=dict(FunctionCall=dict(
                                allowance=None, receiver_id="captured.near", method_names=["read"])))
                            rows = [dict(version=tag, nonceMode=mode, nonce=nonce, receiverId="fixture-caller.near" if index % 3 == 0 else "captured.near",
                                blockHash=[index + 1] * 32, actions=[dict(Transfer=dict(deposit="1"))] if index % 2 == 0 else [
                                    dict(FunctionCall=dict(method_name="read", args="", gas=10**12, deposit="0"))])
                                for index, (tag, mode, nonce) in enumerate(vectors)]
                            if height == 1: rows[-1]["nonce"] = 1_000_000
                            first = contract_probe.block(height, rows, gas_limit=0)
                            first["gasPrice"] = price
                            scenario = dict(caller=caller, blocks=[first])
                            target = Path(directory) / f"{protocol}-{key}-{policy}"
                            importer.prepare(contract_probe.snapshot(protocol), target, reference=REFERENCE, model=CHAIN, scenario=scenario)
                            original = json.loads((target / "native.json").read_text())
                            replay = json.loads((target / "model.json").read_text())
                            codes = copy.deepcopy(replay["codes"])
                            for code in codes:
                                for field in ["codePath", "watPath"]: code[field] = str(target / code[field])
                            request = dict(formatVersion=1, codes=codes, transactions=[dict(transaction=value, blockHash=rows[index]["blockHash"])
                                for index, value in enumerate(replay["blocks"][0]["transactions"])], admission=dict(
                                configDir=str(target / "configs"), protocolVersion=protocol, blockHeight=height,
                                gasPrice=original["blocks"][0]["gasPrice"], initialState=replay["initialState"], receiptIds=[]))
                            expected = importer.execute(native, original, target)
                            ordinary = importer.execute(CHAIN, replay, target)
                            actual = importer.execute(model, request, ROOT)
                            receipts = []
                            for index, (outcome, attempt) in enumerate(zip(expected["blocks"][0]["outcomes"], actual["registry"]["attempts"])):
                                self.assertEqual(attempt["index"], index)
                                signed_body = expected["blocks"][0]["inputs"]["transactions"][index]
                                self.assertEqual(actual["transactions"][index]["body"], signed_body["borsh"][:-(65 if key == "ed25519" else 66)])
                                self.assertEqual(actual["transactions"][index]["bodySize"], signed_body["bodySize"])
                                self.assertEqual(b58encode(bytes(actual["transactions"][index]["hash"])), outcome["id"])
                                success = outcome["outcome"]["status"].get("SuccessReceiptId")
                                if success is None:
                                    self.assertIsNone(attempt["receipt"]); self.assertIsNone(attempt["receiptHash"])
                                    self.assertIsNotNone(attempt["error"])
                                else:
                                    self.assertIsNone(attempt["error"])
                                    self.assertEqual(b58encode(bytes(attempt["receiptHash"])), success)
                                    receipts.append([attempt["receipt"]["receiptId"], attempt["receiptHash"]])
                            self.assertEqual(len(actual["registry"]["attempts"]), len(rows))
                            self.assertEqual(actual["registry"]["receiptIds"], receipts)
                            self.assertEqual(actual["registry"]["actionFormats"], [[id, "legacy"] for id, _ in receipts])
                            projected = comparator.Projection({code["hash"]: Path(code["codePath"]).read_bytes() for code in codes}).project(original, expected, replay)
                            projected_state = copy.deepcopy(projected["blocks"][0]["state"])
                            projected_state["delayed"] = []  # The preflight observes conversions, before queue insertion.
                            self.assertEqual(canonical_state(actual["registry"]["stateAfterTransactions"]), canonical_state(projected_state))
                            observed_state = copy.deepcopy(ordinary["blocks"][0]["state"])
                            delayed = observed_state["delayed"]
                            queue_request = dict(formatVersion=1, codes=codes, initialState=observed_state,
                                runtimeConfig=dict(configDir=str(target / "configs"), protocolVersion=protocol), queueContext=dict(
                                    receiptIds=receipts, dataIds=[], actionFormats=actual["registry"]["actionFormats"],
                                    delayed=None if not delayed else dict(firstIndex=0, forms=[dict(kind="newStored") for _ in delayed])))
                            encoded_queue = importer.execute(state_model, queue_request, ROOT)
                            native_queue = [row for row in expected["blocks"][0]["state"]["entries"] if row[0][0] in [3, 4, 5, 6, 7]]
                            self.assertEqual(entries(encoded_queue["queueEntries"]), entries(native_queue))
                            evidence.append(dict(protocol=protocol, keyType=key, policy=policy, scenario=scenario, originalRequest=original,
                                native=expected, ordinaryModel=ordinary, request=request, model=actual, queueRequest=queue_request, encodedQueue=encoded_queue))
        atomic_write(ROOT / "audit/transaction-registry-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, stateEncoderSha256=state_checksum, automaticTransactionReceiptRegistration=True,
            generalRuntimeIdentityRegistration=False, cases=evidence), indent=2) + "\n").encode())

    def test_malformed_unencodable_bodies_and_identity_collisions_fail_closed(self):
        variants = []
        for width in [0, 31, 33]:
            value = source(); value["transactions"][0]["blockHash"] = [0] * width; variants.append(value)
        for patch in [dict(version=2), dict(version=0, nonceMode="strict"), dict(nonce=2**64),
                dict(publicKey=[3] * 33), dict(signerId="Bad.near")]:
            value = source(); value["transactions"][0]["transaction"].update(patch); variants.append(value)
        value = source(); value["transactions"][0]["transaction"]["actions"] = [dict(kind="deployContract", codeHash="missing")]; variants.append(value)
        # A valid accepted transaction must not silently overwrite a preexisting logical ID.
        value = source(); value["admission"] = dict(configDir=str(ROOT / "near-lean/vm/configs"), protocolVersion=86,
            blockHeight=101, gasPrice="100000000", initialState=empty_state(), receiptIds=[[1, [1] * 32]])
        variants.append(value)
        with frozen_model(MODEL) as (model, _):
            for value in variants:
                with self.subTest(request=value):
                    result = subprocess.run([str(model)], input=json.dumps(value), text=True, capture_output=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertTrue(result.stderr)


if __name__ == "__main__":
    unittest.main()
