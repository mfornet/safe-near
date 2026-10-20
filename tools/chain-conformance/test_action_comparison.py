#!/usr/bin/env python3
"""Native administrative actions, typed failures and receipt rollback."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import action_probe as corpus
import compare_fixture as comparator
from gas_probe import differences
from prepare import HERE, ROOT, atomic_write

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


class ActionComparisonTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/action-chain-regressions.json",
            (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def test_administrative_actions_failure_indices_and_rollback(self):
        with tempfile.TemporaryDirectory() as directory:
            for version in [83, 84, 85, 86]:
                for name, (_, _, expected_index) in corpus.CASES.items():
                    with self.subTest(protocol=version, scenario=name):
                        target = Path(directory) / f"{version}-{name}"
                        report = corpus.run_case(version, name, target, REFERENCE, MODEL)
                        self.evidence.append(dict(protocol=version, scenario=name, comparison=report))
                        self.assertIsNone(report["projectionError"])
                        self.assertEqual(report["differences"], [])
                        model = report["model"]
                        self.assertTrue(model["quiescent"])
                        failures = [row["outcome"]["status"] for block in model["blocks"]
                            for row in block["outcomes"] if row["outcome"]["status"]["kind"] == "failure"]
                        if expected_index == "success":
                            self.assertEqual(failures, [])
                        else:
                            self.assertEqual(len(failures), 1)
                            self.assertEqual(failures[0]["actionIndex"], expected_index)
                            expected = comparator.canonical_trace(report["expected"])
                            changed = copy.deepcopy(model)
                            failure = next(row["outcome"]["status"] for block in changed["blocks"]
                                for row in block["outcomes"] if row["outcome"]["status"]["kind"] == "failure")
                            failure["error"], failure["message"] = "different pretty repr", "different display text"
                            self.assertEqual(expected, comparator.canonical_trace(changed, model_output=True))
                            failure["actionIndex"] = 99
                            self.assertTrue(differences(expected, comparator.canonical_trace(changed, model_output=True), "trace"))
                            failure["actionIndex"] = expected_index
                            failure["details"]["kind"] = "differentSemanticError"
                            self.assertTrue(differences(expected, comparator.canonical_trace(changed, model_output=True), "trace"))
                        state = model["blocks"][-1]["state"]
                        if name in {"duplicate-new-key", "late-missing-key"}:
                            self.assertNotIn("new." + corpus.CALLER, dict(state["accounts"]))
                        if name in {"add-key", "add-key-late"}:
                            key = next(key for (owner, public_key), key in state["accessKeys"]
                                if public_key == [0] * 33 and owner == (corpus.CALLER if name == "add-key" else "new." + corpus.CALLER))
                            self.assertEqual(key["nonce"], (100 if name == "add-key" else 109) * 10**6)


if __name__ == "__main__":
    unittest.main()
