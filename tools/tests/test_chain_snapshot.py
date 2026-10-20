"""Offline input/publication checks for captured-account chain imports."""
import base64
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "chain-conformance"))
import import_snapshot as importer


def snapshot():
    code = b"\0asm\1\0\0\0"
    return {"format": "safe-near-snapshot-v1", "block": {"header": {"height": 100, "hash": "1" * 32}},
            "protocol_config": {"protocol_version": 86}, "accounts": [{
                "account_id": "captured.near", "account": {"amount": "1000", "locked": "5",
                "code_hash": importer.code_hash(code), "storage_usage": 200, "storage_paid_at": 0},
                "code": {"hash": importer.code_hash(code), "code_base64": base64.b64encode(code).decode()},
                "access_keys": [{"public_key": "ed25519:" + "1" * 32,
                                 "access_key": {"nonce": 9, "permission": "FullAccess"}}],
                "gas_key_nonces": [], "storage": {"complete": True, "prefixes_base64": [""],
                "values": [{"key": "", "value": "AP8="}]}}]}


class ChainSnapshotTests(unittest.TestCase):
    def test_validated_projection_preserves_values(self):
        original = snapshot()
        before = copy.deepcopy(original)
        rows, codes, version = importer.validate_snapshot(original)
        self.assertEqual(original, before)
        self.assertEqual(version, 86)
        self.assertEqual(rows[0]["storage"], [[[], [0, 255]]])
        self.assertEqual(rows[0]["locked"], "5")
        self.assertEqual(rows[0]["keys"][0]["accessKey"]["nonce"], 9)
        self.assertEqual(list(codes.values()), [b"\0asm\1\0\0\0"])
        original["accounts"][0]["account"]["code_hash"] = importer.EMPTY_CODE_HASH
        original["accounts"][0]["code"] = None
        rows, codes, _ = importer.validate_snapshot(original)
        self.assertIsNone(rows[0]["code"])
        self.assertEqual(codes, {})

    def test_incomplete_duplicate_unsupported_and_malformed_inputs_fail(self):
        changes = [
            lambda x: x.update(format="unknown"),
            lambda x: x["protocol_config"].update(protocol_version=87),
            lambda x: x["accounts"].append(x["accounts"][0]),
            lambda x: x["accounts"][0]["storage"].update(complete=False),
            lambda x: x["accounts"][0]["storage"].update(prefixes_base64=["U1RBVEU="]),
            lambda x: x["accounts"][0]["storage"]["values"].append({"key": "", "value": "AA=="}),
            lambda x: x["accounts"][0]["account"].update(global_contract_hash="hash"),
            lambda x: x["accounts"][0]["account"].update(storage_paid_at=4),
            lambda x: x["accounts"][0]["account"].update(amount=str(2 ** 128)),
            lambda x: x["accounts"][0]["account"].update(storage_usage=True),
            lambda x: x["accounts"][0]["code"].update(hash="wrong"),
            lambda x: x["accounts"][0].update(code=None),
            lambda x: x["accounts"][0].update(gas_key_nonces=[{"nonces": [1]}]),
            lambda x: x["accounts"][0]["access_keys"].append(x["accounts"][0]["access_keys"][0]),
            lambda x: x["accounts"][0]["access_keys"][0]["access_key"].update(nonce=2 ** 64),
            lambda x: x["accounts"][0]["access_keys"][0]["access_key"].update(permission={"GasKeyFullAccess": {}}),
            lambda x: x["accounts"][0]["access_keys"][0].update(public_key="p256:unknown"),
        ]
        for i, change in enumerate(changes):
            with self.subTest(case=i):
                value = snapshot()
                change(value)
                with self.assertRaises(ValueError):
                    importer.validate_snapshot(value)

    def test_function_key_permissions_are_not_coerced(self):
        raw = {"FunctionCall": {"allowance": None, "receiver_id": "contract.near", "method_names": []}}
        value = importer.permission(raw)
        self.assertIsNone(value["allowance"])
        self.assertEqual(value["methodNames"], [])
        raw["FunctionCall"]["allowance"] = "7"
        raw["FunctionCall"]["method_names"] = ["one", "two"]
        self.assertEqual(importer.permission(raw)["allowance"], "7")
        raw["FunctionCall"]["unrecognized"] = True
        with self.assertRaises(ValueError):
            importer.permission(raw)

    def test_publication_preserves_existing_destinations_and_publishes_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stage = root / "stage"
            stage.mkdir()
            (stage / "codes").mkdir()
            (stage / "codes/code.wasm").write_bytes(b"code")
            for name in ("native.json", "model.json", "registered.json", "manifest.json"):
                (stage / name).write_text("{}")
            output = root / "output"
            importer.publish(stage, output)
            self.assertEqual((output / "codes/code.wasm").read_bytes(), b"code")
            self.assertTrue((output / "manifest.json").exists())
            with self.assertRaises(FileExistsError):
                importer.publish(stage, output)
            self.assertEqual((output / "native.json").read_text(), "{}")


    def test_incomplete_registered_stage_is_not_published(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); stage = root / "stage"; stage.mkdir()
            for name in ["native.json", "model.json", "manifest.json"]: (stage / name).write_text("{}")
            output = root / "output"
            with self.assertRaisesRegex(ValueError, "incomplete fixture"):
                importer.publish(stage, output)
            self.assertFalse(output.exists())

    def test_represented_entry_comparison_rejects_duplicates_extras_and_invalid_bytes(self):
        self.assertEqual(importer.canonical_entries([[[9, 1], []], [[0, 2], [255]]]), [[[0, 2], [255]], [[9, 1], []]])
        for rows in [[[[0], []], [[0], [1]]], [[[8], []]], [[[0], [True]]], [[[0], [256]]], [[[], []]]]:
            with self.subTest(rows=rows), self.assertRaises(ValueError): importer.canonical_entries(rows)


if __name__ == "__main__":
    unittest.main()
