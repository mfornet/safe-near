#!/usr/bin/env python3
"""Exact native contract comparisons, including chunk trie accounting."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
import contract_probe as corpus
from gas_probe import differences
from prepare import HERE, ROOT, atomic_write

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


class ContractComparisonTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        path = ROOT / "audit/contract-chain-regressions.json"
        atomic_write(path, (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def test_read_panic_and_callback_delivery_schedules_across_protocols(self):
        with tempfile.TemporaryDirectory() as directory:
            number = 0
            for version in [83, 84, 85, 86]:
                cases = [(method, "all") for method in ["read", "fail", "spawn", "spawn_fail"]]
                cases += [("spawn", schedule) for schedule in corpus.SCHEDULES if schedule != "all"]
                for method, schedule in cases:
                    with self.subTest(protocol=version, method=method, schedule=schedule):
                        report = corpus.run_case(version, method, schedule, Path(directory) / str(number), REFERENCE, MODEL)
                        number += 1
                        self.evidence.append(dict(protocol=version, method=method, schedule=schedule, expectedToMatch=True, comparison=report))
                        self.assertIsNone(report["projectionError"])
                        self.assertEqual(report["differences"], [])
                        if schedule == "unfinished":
                            self.assertFalse(report["model"]["quiescent"])
                        else:
                            self.assertTrue(report["model"]["quiescent"])
                        if schedule == "callback-first":
                            self.assertTrue(report["model"]["blocks"][2]["state"]["postponed"])
                            self.assertTrue(report["model"]["blocks"][2]["state"]["pendingDataCount"])
                            self.assertTrue(report["model"]["blocks"][2]["state"]["postponedByData"])
                        if schedule == "data-first":
                            self.assertTrue(report["model"]["blocks"][3]["state"]["receivedData"])
                        if schedule == "delayed":
                            self.assertTrue(report["model"]["blocks"][2]["state"]["delayed"])

    def test_zero_budget_defers_signer_is_receiver_receipt(self):
        import import_snapshot as importer
        request = corpus.scenario("read")
        request["blocks"] = request["blocks"][:1]
        request["blocks"][0]["gasLimit"] = 0
        request["blocks"][0]["transactions"][0].update(receiverId="fixture-caller.near", actions=[{"Transfer": {"deposit": "1"}}])
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "fixture"
            importer.prepare(corpus.snapshot(), target, reference=REFERENCE, model=MODEL, scenario=request)
            report = comparator.compare(target, REFERENCE, MODEL)
            self.evidence.append(dict(method="self-transfer", schedule="zero-budget", expectedToMatch=True, comparison=report))
            self.assertIsNone(report["projectionError"])
            self.assertEqual(report["differences"], [])
            self.assertEqual(len(report["model"]["blocks"][0]["state"]["delayed"]), 1)
            self.assertEqual(len(report["model"]["blocks"][0]["outcomes"]), 1)
            self.assertFalse(report["model"]["quiescent"])

    def test_storage_mutations_match_all_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            for version in [83, 84, 85, 86]:
                for method in ["write", "remove", "panic_after_write"]:
                    with self.subTest(protocol=version, method=method):
                        report = corpus.run_case(version, method, "all", Path(directory) / f"{version}-{method}", REFERENCE, MODEL)
                        self.evidence.append(dict(protocol=version, method=method, schedule="all", expectedToMatch=True, comparison=report))
                        self.assertIsNone(report["projectionError"])
                        self.assertEqual(report["differences"], [])
                        native = report["native"]["blocks"][1]["outcomes"][0]["outcome"]
                        model = report["model"]["blocks"][1]["outcomes"][0]["outcome"]
                        storage_costs = {row["cost"]: int(row["gas_used"]) for row in native["metadata"]["gas_profile"]}
                        costs = json.loads((ROOT / f"near-lean/vm/configs/runtime_config_v{version}.json").read_text())["wasm_config"]["ext_costs"]
                        old_value_cost = "storage_remove_ret_value_byte" if method == "remove" else "storage_write_evicted_byte"
                        self.assertEqual(storage_costs.get(old_value_cost.upper(), 0), 5 * costs[old_value_cost])
                        external_cost = sum(storage_costs.get(name, 0) for name in ["TOUCHING_TRIE_NODE", "READ_CACHED_TRIE_NODE"])
                        self.assertGreater(external_cost, 0)
                        self.assertEqual(native["gas_burnt"], model["gasBurnt"])
                        left, right = comparator.canonical_trace(report["expected"]), comparator.canonical_trace(report["model"])
                        for a, b in zip(left["blocks"], right["blocks"]):
                            self.assertEqual(a["state"]["storage"], b["state"]["storage"])
                            self.assertEqual(a["state"]["accessKeys"], b["state"]["accessKeys"])
                        final_storage = dict(right["blocks"][-1]["state"]["storage"])
                        if method == "write":
                            self.assertEqual(final_storage["captured.near"], [[[107], [118, 255]]])
                        elif method == "remove":
                            self.assertNotIn("captured.near", final_storage)
                        else:
                            self.assertEqual(final_storage["captured.near"], [[[107], list(b"hello")]])

    def test_comparison_rejects_asset_and_context_drift_and_detects_field_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture"
            report = corpus.run_case(86, "spawn", "all", path, REFERENCE, MODEL)
            self.assertEqual(report["differences"], [])
            for field in ["nextId", "accounts", "receivedData", "postponed", "accessKeys"]:
                altered = copy.deepcopy(report["model"])
                altered["blocks"][1]["state"][field] = "changed"
                self.assertTrue(differences(comparator.canonical_trace(report["expected"]), altered))
            altered = copy.deepcopy(report["model"])
            altered["blocks"][1]["outcomes"][0]["outcome"]["gasBurnt"] += 1
            self.assertTrue(differences(report["expected"], altered))
            source = json.loads((path / "native.json").read_text())
            request = json.loads((path / "model.json").read_text())
            request["blocks"][0]["blockHeight"] += 1
            codes = {code["hash"]: (path / code["codePath"]).read_bytes() for code in request["codes"]}
            with self.assertRaisesRegex(ValueError, "context differs"):
                comparator.Projection(codes).project(source, report["native"], request)
            (path / "native.json").write_text("{}")
            with self.assertRaisesRegex(ValueError, "asset hash mismatch"):
                comparator.compare(path, REFERENCE, MODEL)


if __name__ == "__main__":
    unittest.main()
