#!/usr/bin/env python3
"""Observe native action-derived VM seeds through real contract execution."""
import base64
import copy
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
import contract_probe as corpus
import import_snapshot as importer
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference
from test_receipt_registry import CHAIN, MODEL, request_for
from test_state_encoding import entries
from trie_probe import REFERENCE, frozen_model


def snapshot(protocol):
    value = corpus.snapshot(protocol)
    blob = (HERE / "fixtures/action_randomness.wasm").read_bytes()
    for row in value["accounts"]:
        row["account"].update(code_hash=importer.code_hash(blob), storage_usage=len(blob) + 228)
        row["code"] = dict(hash=importer.code_hash(blob), code_base64=base64.b64encode(blob).decode())
    return value


def scenario(protocol, key, kind):
    value = corpus.scenario("spawn", "callback-first" if kind == "spawn" else "all")
    value["caller"]["keyType"] = key
    transaction = value["blocks"][0]["transactions"][0]
    call = transaction["actions"][0]["FunctionCall"]
    call["method_name"] = "spawn_seed" if kind == "spawn" else "seed"
    if kind == "twice":
        call["gas"] = 60 * 10**12
        transaction["actions"].append(copy.deepcopy(transaction["actions"][0]))
    if kind == "offset": transaction["actions"].insert(0, dict(Transfer=dict(deposit="0")))
    if kind == "local":
        transaction["receiverId"] = value["caller"]["accountId"]
        transaction["actions"].insert(0, dict(DeployContract=dict(code=base64.b64encode(
            (HERE / "fixtures/action_randomness.wasm").read_bytes()).decode())))
    if kind == "delayed": value["blocks"][1]["gasLimit"] = 0
    for block in value["blocks"]:
        height = block["blockHeight"]
        block["randomSeed"] = [(protocol + height + 3 * index) % 256 for index in range(32)]
        block["prevBlockHash"] = [(height + 7 * index) % 256 for index in range(32)]
    return value


class ActionRandomnessTests(unittest.TestCase):
    def test_vm_observes_original_action_position_parent_and_execution_height(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum), frozen_model(CHAIN) as (chain, ordinary_checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for key in ["ed25519", "secp256k1"]:
                    for kind in ["single", "twice", "offset", "local", "delayed", "spawn"]:
                        with self.subTest(protocol=protocol, key=key, kind=kind):
                            original_scenario = scenario(protocol, key, kind)
                            captured = snapshot(protocol)
                            if kind == "delayed":
                                planning = Path(directory) / f"plan-{protocol}-{key}"
                                importer.prepare(captured, planning, reference=REFERENCE, model=chain, scenario=original_scenario)
                                source = json.loads((planning / "native.json").read_text())
                                headers = source["blocks"]; source["blocks"] = []; previous = None
                                for block, specification in zip(headers, original_scenario["blocks"]):
                                    if previous is not None:
                                        block["congestionInfo"] = previous
                                        specification["congestionInfo"] = previous
                                    source["blocks"].append(block)
                                    previous = importer.execute(native, source, planning)["blocks"][-1]["nextCongestionInfo"]
                            target = Path(directory) / f"{protocol}-{key}-{kind}"
                            importer.prepare(captured, target, reference=REFERENCE, model=chain, scenario=original_scenario)
                            original = json.loads((target / "native.json").read_text())
                            expected = importer.execute(native, original, target)
                            request = request_for(target, original_scenario)
                            actual = importer.execute(model, request, ROOT)
                            self.assertTrue(actual["nativeActionRandomness"])
                            registries = [row["registry"] for row in actual["blocks"]]
                            catalogue = {code["hash"]: Path(code["codePath"]).read_bytes() for code in request["codes"]}
                            projected = comparator.Projection(catalogue, registries=registries).project(original, expected, request)
                            ordinary_shape = {name: actual[name] for name in projected if name != "blocks"}
                            ordinary_shape["blocks"] = [row["execution"] for row in actual["blocks"]]
                            self.assertEqual(comparator.canonical_trace(projected), comparator.canonical_trace(ordinary_shape))
                            for left, right in zip(expected["blocks"], actual["blocks"]):
                                self.assertEqual([row["bytes"] for row in right["outgoingBytes"]], left["outgoingReceiptBorsh"])
                                queue = [row for row in left["state"]["entries"] if row[0][0] in [3, 4, 5, 6, 7]]
                                self.assertEqual(entries(right["queueEntries"]), entries(queue))
                            logged = [(index, outcome["outcome"]["logs"]) for index, block in enumerate(actual["blocks"])
                                for outcome in block["execution"]["outcomes"] if outcome["outcome"]["logs"]]
                            self.assertEqual(sum(len(logs) for _, logs in logged), 3 if kind == "spawn" else 2 if kind == "twice" else 1)
                            self.assertTrue(all(len(seed) == 64 for _, logs in logged for seed in logs))
                            if kind == "twice": self.assertNotEqual(*logged[0][1])
                            self.assertEqual(logged[0][0], 0 if kind == "local" else 2 if kind == "delayed" else 1)
                            if kind == "spawn": self.assertGreater(logged[-1][0], 2)
                            evidence.append(dict(protocol=protocol, keyType=key, kind=kind, originalRequest=original,
                                native=expected, request=request, model=actual))
        atomic_write(ROOT / "audit/action-randomness-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, ordinaryModelBinarySha256=ordinary_checksum, actionRandomnessIntegrated=True, nativeGeneratedSeedAsInput=False,
            cases=evidence), indent=2) + "\n").encode())


if __name__ == "__main__":
    unittest.main()
