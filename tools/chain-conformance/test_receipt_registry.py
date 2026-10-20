#!/usr/bin/env python3
"""Actual runtime births -> native receipt bytes and persistent queue records."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import compare_fixture as comparator
import contract_probe as corpus
import import_snapshot as importer
from prepare import ROOT, atomic_write
from probe import frozen_reference
from test_state_encoding import entries
from trie_probe import REFERENCE, frozen_model

CHAIN = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/registered-replay"


def request_for(target, scenario):
    request = json.loads((target / "model.json").read_text())
    request["transactionBlockHashes"] = [[tx.get("blockHash", block["prevBlockHash"])
        for tx in block["transactions"]] for block in scenario["blocks"]]
    for code in request["codes"]:
        for field in ["codePath", "watPath"]:
            code[field] = str(target / code[field])
    request["configDir"] = str(target / request["configDir"])
    return request


class ReceiptRegistryTests(unittest.TestCase):
    def test_original_transactions_actual_births_and_queue_bytes(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum), frozen_model(CHAIN) as (chain, ordinary_checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for method in ["spawn", "spawn_fail", "twice", "offset", "rollback"]:
                    with self.subTest(protocol=protocol, method=method):
                        target = Path(directory) / f"{protocol}-{method}"
                        scenario = corpus.scenario("spawn_fail" if method == "spawn_fail" else "spawn")
                        actions = scenario["blocks"][0]["transactions"][0]["actions"]
                        if method in {"twice", "rollback"}:
                            actions.append(copy.deepcopy(actions[0]))
                            for action in actions: action["FunctionCall"]["gas"] = 120 * 10**12
                            if method == "rollback": actions[-1]["FunctionCall"]["method_name"] = "fail"
                        if method == "offset": actions.insert(0, dict(Transfer=dict(deposit="0")))
                        importer.prepare(corpus.snapshot(protocol), target, reference=REFERENCE, model=chain, scenario=scenario)
                        original = json.loads((target / "native.json").read_text())
                        expected = importer.execute(native, original, target)
                        ordinary = importer.execute(chain, json.loads((target / "model.json").read_text()), target)
                        request = request_for(target, scenario)
                        actual = importer.execute(model, request, ROOT)
                        self.check_trace(expected, ordinary, actual)
                        catalogue = {code["hash"]: Path(code["codePath"]).read_bytes() for code in request["codes"]}
                        registries = [row["registry"] for row in actual["blocks"]]
                        projected = comparator.Projection(catalogue, registries=registries).project(original, expected, request)
                        self.assertEqual(comparator.canonical_trace(projected), comparator.canonical_trace(ordinary))
                        if protocol == 86 and method == "offset":
                            invalid = []
                            extra = copy.deepcopy(registries); extra[1]["receiptIds"].append([999, [255] * 32]); invalid.append(extra)
                            alias = copy.deepcopy(registries); alias[1]["dataIds"][0]["id"] = 1; invalid.append(alias)
                            owner = copy.deepcopy(registries); owner[1]["dataIds"][0]["receiverId"] = "wrong.near"; invalid.append(owner)
                            for context in invalid:
                                with self.assertRaises(ValueError):
                                    comparator.Projection(catalogue, registries=context).project(original, expected, request)
                            changed = copy.deepcopy(request)
                            changed["transactionBlockHashes"][0][0][0] ^= 1
                            altered = importer.execute(model, changed, ROOT)
                            self.assertNotEqual(altered["blocks"][0]["outgoingBytes"], actual["blocks"][0]["outgoingBytes"])
                        roots = actual["blocks"][1]["identityBirths"]
                        if method == "rollback":
                            self.assertEqual(roots[0]["vmActions"], [])
                            self.assertEqual(actual["blocks"][-1]["registry"]["dataIds"], [])
                        else:
                            calls = roots[0]["vmActions"]
                            self.assertEqual([call["actionIndex"] for call in calls], [0, 1] if method == "twice" else [1] if method == "offset" else [0])
                            self.assertTrue(all(len(call["data"]) == 1 for call in calls))
                        evidence.append(dict(protocol=protocol, method=method, originalRequest=original, native=expected,
                            request=request, model=actual))
        atomic_write(ROOT / "audit/receipt-registry-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, ordinaryModelBinarySha256=ordinary_checksum, automaticRuntimeIdentityRegistration=True, nativeGeneratedIdentitiesAsInputs=False,
            vmActionRandomnessIntegrated=True, cases=evidence), indent=2) + "\n").encode())

    def check_trace(self, native, ordinary, registered):
        self.assertEqual(registered["stop"], ordinary["stop"])
        self.assertEqual(len(registered["blocks"]), len(native["blocks"]))
        for left, right, plain in zip(native["blocks"], registered["blocks"], ordinary["blocks"]):
            self.assertEqual(right["execution"], plain)
            self.assertEqual([row["bytes"] for row in right["outgoingBytes"]], left["outgoingReceiptBorsh"])
            expected = [row for row in left["state"]["entries"] if row[0][0] in [3, 4, 5, 6, 7]]
            self.assertEqual(entries(right["queueEntries"]), entries(expected))

    def test_callback_delivery_and_persistent_queue_lifetimes(self):
        evidence = []
        with frozen_model(MODEL) as (model, checksum), frozen_model(CHAIN) as (chain, ordinary_checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for schedule in ["callback-first", "data-first", "delayed"]:
                    with self.subTest(protocol=protocol, schedule=schedule):
                        target = Path(directory) / f"{protocol}-{schedule}"
                        origin = corpus.run_case(protocol, "spawn", schedule, target, REFERENCE, chain)
                        self.assertEqual(origin["differences"], [])
                        scenario = corpus.scenario("spawn", schedule)
                        request = request_for(target, scenario)
                        actual = importer.execute(model, request, ROOT)
                        self.check_trace(origin["native"], origin["model"], actual)
                        if schedule == "delayed":
                            delayed = [row["registry"]["delayed"] for row in actual["blocks"]]
                            self.assertIsNone(delayed[1])
                            self.assertTrue(delayed[2]["forms"])
                            self.assertTrue(all(form["kind"] == "storedV1" for form in delayed[2]["forms"]))
                            self.assertEqual(delayed[-1], dict(firstIndex=len(delayed[2]["forms"]), forms=[]))
                        evidence.append(dict(protocol=protocol, schedule=schedule, request=request, model=actual, origin=origin))
        atomic_write(ROOT / "audit/receipt-registry-queues.json", (json.dumps(dict(modelBinarySha256=checksum, ordinaryModelBinarySha256=ordinary_checksum,
            nativeGeneratedIdentitiesAsInputs=False, cases=evidence), indent=2) + "\n").encode())

    def test_missing_original_hashes_and_missing_parent_bindings_fail_closed(self):
        from test_replay import empty_state, action_receipt
        base = dict(formatVersion=1, protocolVersion=86, configDir=str(ROOT / "near-lean/vm/configs"), codes=[],
            initialState=empty_state(), pendingReceipts=[], blocks=[], transactionBlockHashes=[])
        variants = []
        request = copy.deepcopy(base); request["transactionBlockHashes"] = [[]]; variants.append(request)
        request = copy.deepcopy(base); request["pendingReceipts"] = [action_receipt([])]; variants.append(request)
        request = copy.deepcopy(base); request["queueContext"] = dict(receiptIds=[[1, [0] * 31]], dataIds=[], actionFormats=[[1, "legacy"]], delayed=None); variants.append(request)
        owner = copy.deepcopy(base)
        owner["pendingReceipts"] = [action_receipt([])]
        owner["queueContext"] = dict(receiptIds=[[20, [20] * 32]], actionFormats=[[20, "legacy"]], delayed=None,
            dataIds=[dict(id=40, hash=[40] * 32, receiverId="alice.near"), dict(id=41, hash=[41] * 32, receiverId="alice.near")])
        variants.append(owner)
        with frozen_model(MODEL) as (model, _):
            for request in variants:
                with self.subTest(request=request):
                    result = subprocess.run([str(model)], input=json.dumps(request), text=True, capture_output=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertTrue(result.stderr)
                    if request is owner: self.assertIn("data identity receiver mismatch", result.stderr)

    def test_old_backlog_new_local_and_incoming_queue_context(self):
        from test_delayed_local_order import CALLER, transaction
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum), frozen_model(CHAIN) as (chain, ordinary_checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for key in ["ed25519", "secp256k1"]:
                    with self.subTest(protocol=protocol, key=key):
                        blocks = [corpus.block(101, [transaction(1, 1)], gas_limit=0),
                            corpus.block(102, [transaction(2, 2), transaction(3, 3, "captured.near")], gas_limit=0),
                            corpus.block(103, [transaction(4, 4)], gas_limit=0),
                            corpus.block(104, [transaction(5, 5)]), corpus.block(105)]
                        scenario = dict(caller=dict(accountId=CALLER, seed="automatic-registry-FIFO", keyType=key,
                            amount=str(100 * 10**24)), blocks=blocks)
                        planning = Path(directory) / f"plan-{protocol}-{key}"
                        importer.prepare(corpus.snapshot(protocol), planning, reference=REFERENCE, model=chain, scenario=scenario)
                        original = json.loads((planning / "native.json").read_text())
                        source = {**original, "blocks": []}
                        previous = None
                        for block, specification in zip(original["blocks"], blocks):
                            if previous is not None:
                                block["congestionInfo"] = previous
                                specification["congestionInfo"] = previous
                            source["blocks"].append(block)
                            previous = importer.execute(native, source, planning)["blocks"][-1]["nextCongestionInfo"]
                        target = Path(directory) / f"run-{protocol}-{key}"
                        importer.prepare(corpus.snapshot(protocol), target, reference=REFERENCE, model=chain, scenario=scenario)
                        origin = comparator.compare(target, REFERENCE, chain)
                        self.assertEqual(origin["differences"], [])
                        request = request_for(target, scenario)
                        actual = importer.execute(model, request, ROOT)
                        self.check_trace(origin["native"], origin["model"], actual)
                        queues = [row["registry"]["delayed"] for row in actual["blocks"]]
                        self.assertEqual([len(queue["forms"]) for queue in queues], [1, 2, 4, 0, 0])
                        self.assertEqual([queue["firstIndex"] for queue in queues], [0, 0, 0, 4, 4])
                        self.assertEqual(queues[0]["forms"], queues[2]["forms"][:1])
                        evidence.append(dict(protocol=protocol, keyType=key, scenario=scenario, origin=origin,
                            request=request, model=actual))
        atomic_write(ROOT / "audit/receipt-registry-fifo.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, ordinaryModelBinarySha256=ordinary_checksum, nativeGeneratedIdentitiesAsInputs=False, cases=evidence), indent=2) + "\n").encode())


if __name__ == "__main__":
    unittest.main()
