#!/usr/bin/env python3
"""Native stateless action boundaries, failure precedence and deployment binding."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
from gas_probe import differences
import import_snapshot as importer
import validation_probe as corpus
from prepare import HERE, ROOT, atomic_write

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


class ActionValidationTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/action-validation-regressions.json",
            (json.dumps(dict(cases=cls.evidence), separators=(",", ":")) + "\n").encode())

    def check_case(self, version, name, target):
        report = corpus.run_case(version, name, target, REFERENCE, MODEL)
        self.evidence.append(dict(protocol=version, scenario=name, comparison=report))
        self.assertIsNone(report["projectionError"])
        self.assertEqual(report["differences"], [])
        _, _, expected = corpus.prepare_case(version, name)
        model = report["model"]
        self.assertTrue(model["quiescent"])
        outcomes = [row["outcome"]["status"] for row in model["blocks"][0]["outcomes"]]
        failures = [status for status in outcomes if status["kind"] == "failure"]
        self.assertEqual(len(failures), 0 if expected is None else 1)
        if expected is None:
            return
        status = failures[0]
        self.assertEqual(status["details"]["kind"], "actionsValidation")
        self.assertEqual(status["details"]["error"]["kind"], expected)
        self.assertIsNone(status["actionIndex"])
        if name == "accepted-around-rejected":
            self.assertEqual([status["kind"] == "failure" for status in outcomes], [False, True, False])
            key = next(key for (owner, _), key in model["blocks"][0]["state"]["accessKeys"] if owner == corpus.CALLER)
            self.assertEqual(key["nonce"], 2)
        else:
            self.assertEqual(model["blocks"][0]["state"], model["initialState"])
            for field in ["tokensBurnt", "subsidizedAmount"]:
                self.assertEqual(model["blocks"][0][field], "0")
            self.assertEqual(model["blocks"][0]["outgoingReceipts"], [])
        altered = copy.deepcopy(model)
        error = next(row["outcome"]["status"]["details"]["error"] for row in altered["blocks"][0]["outcomes"]
            if row["outcome"]["status"]["kind"] == "failure")
        field = next((field for field in error if field != "kind"), "kind")
        error[field] = "changed semantic parameter"
        self.assertTrue(differences(comparator.canonical_trace(report["expected"]),
            comparator.canonical_trace(altered, model_output=True), "trace"))

    def test_boundaries_and_precedence_across_protocols(self):
        with tempfile.TemporaryDirectory() as directory:
            for version in [83, 84, 85, 86]:
                for name in corpus.CASES:
                    with self.subTest(protocol=version, scenario=name):
                        self.check_case(version, name, Path(directory) / f"{version}-{name}")
                print(f"protocol {version}: action validation complete", flush=True)

    def test_actual_oversized_arguments_and_code(self):
        with tempfile.TemporaryDirectory() as directory:
            for name in corpus.LARGE_CASES:
                with self.subTest(scenario=name):
                    self.check_case(86, name, Path(directory) / name)

    def test_deployment_bytes_survive_rpc_hashing_and_cannot_be_rebound(self):
        capture = corpus.snapshot(86)
        scenario = dict(caller=dict(accountId=corpus.CALLER, seed="public-deployment-test", amount=str(100 * 10**24)),
            blocks=[corpus.block(101, [dict(receiverId=corpus.CALLER, nonce=1,
                actions=[{"DeployContract": {"code": "AGFzbQEAAAA="}}])])] + [corpus.block(i) for i in range(102, 105)])
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "deployment"
            importer.prepare(capture, target, reference=REFERENCE, model=MODEL, scenario=scenario)
            report = comparator.compare(target, REFERENCE, MODEL)
            self.evidence.append(dict(protocol=86, scenario="deployment-byte-binding", comparison=report))
            self.assertEqual(report["differences"], [])
            caller = dict(report["model"]["blocks"][-1]["state"]["accounts"])[corpus.CALLER]
            self.assertEqual(caller["codeHash"], importer.code_hash(b"\0asm\1\0\0\0"))
            path = target / "model.json"
            request = json.loads(path.read_text())
            request["blocks"][0]["transactions"][0]["actions"][0]["codeHash"] = capture["accounts"][0]["code"]["hash"]
            path.write_text(json.dumps(request))
            manifest_path = target / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["files"]["model.json"] = importer.file_digest(path)
            manifest_path.write_text(json.dumps(manifest))
            changed = comparator.compare(target, REFERENCE, MODEL)
            self.assertIn("model transactions differ", changed["projectionError"])
            self.assertTrue(changed["differences"])


if __name__ == "__main__":
    unittest.main()
