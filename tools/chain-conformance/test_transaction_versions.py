#!/usr/bin/env python3
"""Ordinary-key V0/V1 batches through native signing, apply and Lean replay."""
import copy
import json
from pathlib import Path
import tempfile
import subprocess
import unittest

import compare_fixture as comparator
import import_snapshot as importer
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference
from test_snapshot_import import snapshot, block

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


def requests(version, vectors, height=101):
    capture = snapshot()
    config = json.loads((ROOT / f"near-lean/vm/configs/runtime_config_v{version}.json").read_text())
    capture["protocol_config"] = dict(protocol_version=version, runtime_config={k: v for k, v in config.items()
        if k not in {"runtime_admission", "runtime_finance"}})
    transactions = [dict(version=tag, nonceMode=mode, receiverId="captured.near", nonce=nonce,
        actions=[{"Transfer": {"deposit": "1"}}]) for tag, mode, nonce in vectors]
    scenario = dict(caller=dict(accountId="fixture-caller.near", seed="safe-near-version-test", amount=str(100 * 10**24)),
        blocks=[block(height, transactions)] + [block(height + i) for i in range(1, 4)])
    return capture, scenario


class TransactionVersionTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/transaction-version-comparison.json",
            (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def test_native_version_gates_and_sequential_batch_admission(self):
        vectors = [(0, "monotonic", 1), (1, "strict", 2), (1, "strict", 4),
                   (1, "monotonic", 9), (1, "strict", 10), (0, "monotonic", 11)]
        with tempfile.TemporaryDirectory() as temporary:
            for version in [83, 84, 85, 86]:
                with self.subTest(protocol=version):
                    capture, scenario = requests(version, vectors)
                    target = Path(temporary) / str(version)
                    importer.prepare(capture, target, reference=REFERENCE, model=MODEL, scenario=scenario)
                    report = comparator.compare(target, REFERENCE, MODEL)
                    self.evidence.append(dict(protocol=version, scenario="mixed-batch", comparison=report))
                    self.assertIsNone(report["projectionError"])
                    self.assertEqual(report["differences"], [])
                    outcomes = report["model"]["blocks"][0]["outcomes"]
                    accepted = [o["outcome"]["status"]["kind"] != "failure" for o in outcomes]
                    self.assertEqual(accepted, [True, False, False, False, False, True] if version < 85
                                     else [True, True, False, True, True, True])
                    state = report["model"]["blocks"][-1]["state"]
                    key = next(value for (account, _), value in state["accessKeys"] if account == "fixture-caller.near")
                    self.assertEqual(key["nonce"], 11)
                    self.assertTrue(report["model"]["quiescent"])

    def test_nonce_ceiling_staleness_and_version_gate_precedence(self):
        vectors = [(1, "strict", 0), (0, "monotonic", 0), (0, "monotonic", 999999),
                   (1, "strict", 1000000), (0, "monotonic", 1000000)]
        with tempfile.TemporaryDirectory() as temporary:
            for version in [84, 85, 86]:
                with self.subTest(protocol=version):
                    capture, scenario = requests(version, vectors, height=1)
                    target = Path(temporary) / str(version)
                    importer.prepare(capture, target, reference=REFERENCE, model=MODEL, scenario=scenario)
                    report = comparator.compare(target, REFERENCE, MODEL)
                    self.evidence.append(dict(protocol=version, scenario="ceiling-and-precedence", comparison=report))
                    self.assertIsNone(report["projectionError"])
                    self.assertEqual(report["differences"], [])
                    errors = [o["outcome"]["status"] for o in report["model"]["blocks"][0]["outcomes"]]
                    self.assertIn("invalidTransactionVersion" if version < 85 else "invalidNonce", errors[0]["error"])
                    self.assertIn("nonceTooLarge", errors[-1]["error"])
                    self.assertEqual(errors[2]["kind"], "successReceiptId")

    def test_explicit_defaults_match_but_version_changes_cannot_rebind_signed_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            capture, scenario = requests(86, [(0, "monotonic", 1)])
            target = Path(temporary) / "fixture"
            importer.prepare(capture, target, reference=REFERENCE, model=MODEL, scenario=scenario)
            path = target / "model.json"
            value = json.loads(path.read_text())
            manifest = json.loads((target / "manifest.json").read_text())
            for version in [0, 1]:
                value["blocks"][0]["transactions"][0].update(version=version, nonceMode="monotonic")
                path.write_text(json.dumps(value))
                manifest["files"]["model.json"] = importer.file_digest(path)
                (target / "manifest.json").write_text(json.dumps(manifest))
                report = comparator.compare(target, REFERENCE, MODEL)
                if version == 0:
                    self.assertEqual(report["differences"], [])
                else:
                    self.assertIn("model transactions differ", report["projectionError"])
                    self.assertTrue(report["differences"])

    def test_native_signer_rejects_unencodable_envelopes(self):
        with frozen_reference(REFERENCE) as (native, _):
            value = dict(signerId="caller.near", seed="public-fixture", transactions=[dict(
                receiverId="receiver.near", nonce=1, blockHash=[0] * 32, actions=[{"Transfer": {"deposit": "1"}}])])
            for patch in [dict(version=2), dict(version=True), dict(version=0, nonceMode="strict"),
                          dict(version=1, nonceMode="Strict")]:
                bad = copy.deepcopy(value)
                bad["transactions"][0].update(patch)
                with self.subTest(patch=patch), self.assertRaises(subprocess.CalledProcessError):
                    importer.native_call(native, "--sign-transactions", bad)


if __name__ == "__main__":
    unittest.main()
