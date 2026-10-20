#!/usr/bin/env python3
"""Full native apply comparison for restricted-key admission and failure order."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
from gas_probe import differences
import permission_probe as corpus
from prepare import HERE, ROOT, atomic_write

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


class PermissionComparisonTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/permission-chain-regressions.json",
            (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def test_permissions_error_parameters_precedence_and_atomic_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            for version in [83, 84, 85, 86]:
                for name in corpus.CASES:
                    with self.subTest(protocol=version, scenario=name):
                        report = corpus.run_case(version, name, Path(directory) / f"{version}-{name}", REFERENCE, MODEL)
                        self.evidence.append(dict(protocol=version, scenario=name, comparison=report))
                        self.assertIsNone(report["projectionError"])
                        self.assertEqual(report["differences"], [])
                        model = report["model"]
                        self.assertTrue(model["quiescent"])
                        _, _, expected = corpus.prepare_case(version, name)
                        outcomes = [row["outcome"]["status"] for row in model["blocks"][0]["outcomes"]]
                        failures = [status for status in outcomes if status["kind"] == "failure"]
                        self.assertEqual(len(failures), 0 if expected is None else 1)
                        if expected is None:
                            continue
                        failure = failures[0]
                        self.assertIsNone(failure["actionIndex"])
                        details = failure["details"]
                        self.assertEqual(details.get("reason", details["kind"]), expected)
                        if name == "accepted-around-rejected":
                            self.assertEqual([s["kind"] == "failure" for s in outcomes], [False, True, False])
                            key = next(key for (owner, _), key in model["blocks"][0]["state"]["accessKeys"] if owner == corpus.CALLER)
                            self.assertEqual(key["nonce"], 2)
                        else:
                            self.assertEqual(model["blocks"][0]["state"], model["initialState"])
                            self.assertEqual(model["blocks"][0]["outgoingReceipts"], [])
                        altered = copy.deepcopy(model)
                        status = next(row["outcome"]["status"] for row in altered["blocks"][0]["outcomes"]
                            if row["outcome"]["status"]["kind"] == "failure")
                        field = next(key for key in status["details"] if key not in {"kind", "reason"}) if len(details) > 2 else "reason"
                        status["details"][field] = "altered semantic parameter"
                        self.assertTrue(differences(comparator.canonical_trace(report["expected"]),
                            comparator.canonical_trace(altered, model_output=True), "trace"))


if __name__ == "__main__":
    unittest.main()
