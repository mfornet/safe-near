#!/usr/bin/env python3
"""Default fixture comparisons use independently derived native execution identities."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import compare_fixture as comparator
import import_snapshot as importer
from prepare import ROOT, atomic_write
from probe import frozen_reference
from test_action_randomness import scenario, snapshot
from test_receipt_registry import CHAIN, MODEL
from trie_probe import REFERENCE, frozen_model


def update_asset(target, name, value):
    path = target / name
    path.write_text(json.dumps(value))
    manifest_path = target / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["files"][name] = importer.file_digest(path)
    manifest_path.write_text(json.dumps(manifest))


class RegisteredComparisonTests(unittest.TestCase):
    def test_default_compares_seed_observations_and_all_represented_state_bytes(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(CHAIN) as (direct, _), frozen_model(MODEL) as (registered, _), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for key in ["ed25519", "secp256k1"]:
                    for kind in ["single", "twice", "offset", "local", "delayed", "spawn"]:
                        with self.subTest(protocol=protocol, key=key, kind=kind):
                            request = scenario(protocol, key, kind)
                            captured = snapshot(protocol)
                            if kind == "delayed":
                                planning = Path(directory) / f"plan-{protocol}-{key}"
                                importer.prepare(captured, planning, reference=REFERENCE, model=direct,
                                    registered_model=registered, scenario=request)
                                source = json.loads((planning / "native.json").read_text())
                                headers = source["blocks"]; source["blocks"] = []; previous = None
                                for block, original in zip(headers, request["blocks"]):
                                    if previous is not None:
                                        block["congestionInfo"] = previous; original["congestionInfo"] = previous
                                    source["blocks"].append(block)
                                    previous = importer.execute(native, source, planning)["blocks"][-1]["nextCongestionInfo"]
                            target = Path(directory) / f"{protocol}-{key}-{kind}"
                            manifest = importer.prepare(captured, target, reference=REFERENCE, model=direct,
                                registered_model=registered, scenario=request)
                            self.assertTrue(manifest["representedGenesisBytesMatch"])
                            self.assertEqual(manifest["defaultExecutionMode"], "registered")
                            report = comparator.compare(target, REFERENCE, direct, registered_model=registered)
                            self.assertEqual(report["executionMode"], "registered")
                            self.assertIsNone(report["projectionError"])
                            self.assertEqual(report["differences"], [])
                            self.assertTrue(report["registered"]["nativeActionRandomness"])
                            self.assertNotIn("native hash generation (event-based renaming)", report["unmodeledObservations"])
                            evidence.append(dict(protocol=protocol, keyType=key, kind=kind, comparison=report))
        atomic_write(ROOT / "audit/default-registered-comparison.json", (json.dumps(dict(referenceBuild=build,
            defaultExecutionMode="registered", cases=evidence), indent=2) + "\n").encode())

    def test_rejected_transaction_hashes_are_compared_even_without_created_receipts(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "rejected"
            request = scenario(86, "ed25519", "single")
            request["blocks"][0]["transactions"][0]["nonce"] = 0
            importer.prepare(snapshot(86), target, reference=REFERENCE, model=CHAIN, scenario=request)
            baseline = comparator.compare(target, REFERENCE, CHAIN)
            self.assertEqual(baseline["differences"], [])
            self.assertTrue(all(not block["outgoingReceipts"] for block in baseline["model"]["blocks"]))
            changed = json.loads((target / "registered.json").read_text())
            changed["transactionBlockHashes"][0][0][0] ^= 1
            update_asset(target, "registered.json", changed)
            report = comparator.compare(target, REFERENCE, CHAIN)
            self.assertIsNone(report["projectionError"])
            self.assertEqual(report["model"], baseline["model"])
            self.assertTrue(any("transactionIdentities" in row["path"] for row in report["differences"]))

    def test_relocation_strict_custody_and_explicit_legacy_mode(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "original"
            importer.prepare(snapshot(86), target, reference=REFERENCE, model=CHAIN,
                scenario=scenario(86, "ed25519", "single"))
            moved = Path(directory) / "moved"; shutil.copytree(target, moved)
            report = comparator.compare(moved, REFERENCE, CHAIN)
            self.assertEqual(report["differences"], [])
            legacy = comparator.compare(moved, REFERENCE, CHAIN, legacy=True)
            self.assertEqual(legacy["executionMode"], "legacy-event-projection")
            self.assertTrue(legacy["differences"])
            with self.assertRaises(FileNotFoundError):
                comparator.compare(moved, REFERENCE, CHAIN, registered_model=Path(directory) / "missing")
            with self.assertRaisesRegex(ValueError, "registered executor provenance"):
                comparator.compare(moved, REFERENCE, CHAIN, registered_model=CHAIN)
            altered = copy.deepcopy(report["registered"])
            altered["blocks"][1]["stateEntries"][0][1][0] ^= 1
            self.assertTrue(comparator.registered_differences(report["native"], altered))
            aliased = copy.deepcopy(report["registered"])
            aliased["blocks"][1]["stateEntries"].append(aliased["blocks"][1]["stateEntries"][0])
            with self.assertRaisesRegex(ValueError, "duplicate represented trie key"):
                comparator.registered_differences(report["native"], aliased)
            manifest = json.loads((moved / "manifest.json").read_text())
            del manifest["registeredModelBinarySha256"]
            (moved / "manifest.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "re-import"):
                comparator.compare(moved, REFERENCE, CHAIN)


if __name__ == "__main__":
    unittest.main()
