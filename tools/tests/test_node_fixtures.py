import json
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import secp_reference  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "near-lean/node/fixtures/types"
SIGNATURES = ROOT / "near-lean/node/fixtures/signatures.jsonl"
HEX = re.compile(r"^(?:[0-9a-f]{2})*$")
LIMIT = 20 * 1024 * 1024


class NodeFixtureTests(unittest.TestCase):
    """The committed Borsh fixtures are well formed and match the protocol pin."""

    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((FIXTURES / "manifest.json").read_text())
        cls.reference = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())

    def test_pin(self):
        self.assertEqual(self.manifest["protocol_version"], self.reference["reference_protocol_version"])
        self.assertEqual(self.manifest["nearcore_release"], self.reference["release"])

    def test_files_match_manifest(self):
        files = {p.stem for p in FIXTURES.glob("*.jsonl")}
        self.assertEqual(files, set(self.manifest["types"]))
        self.assertLess(sum(p.stat().st_size for p in FIXTURES.iterdir()), LIMIT)

    def test_lines(self):
        for name, counts in self.manifest["types"].items():
            accept = reject = 0
            for number, line in enumerate((FIXTURES / f"{name}.jsonl").read_text().splitlines(), 1):
                where = f"{name}:{number}"
                entry = json.loads(line)
                self.assertEqual(entry["type"], name, where)
                self.assertRegex(entry["borsh"], HEX, where)
                if entry.get("reject"):
                    reject += 1
                    self.assertEqual(set(entry), {"type", "name", "borsh", "reject"}, where)
                else:
                    accept += 1
                    for key, value in entry.items():
                        if key not in {"type", "name"}:
                            self.assertTrue(value is None or HEX.match(value), f"{where} {key}")
            self.assertEqual((accept, reject), (counts["accept"], counts["reject"]), name)


class SignatureRecordTests(unittest.TestCase):
    """`signatures.jsonl` records the keys of the oracle's ED25519 and SECP256K1 signatures per
    fixture line."""

    @classmethod
    def setUpClass(cls):
        cls.records = [json.loads(line) for line in SIGNATURES.read_text().splitlines()]
        cls.manifest = json.loads((FIXTURES / "manifest.json").read_text())

    def test_records_name_fixture_lines(self):
        line_counts = {}
        seen = set()
        for record in self.records:
            self.assertEqual(set(record), {"type", "line", "name", "sigs", "signers"}, record["name"])
            key = (record["type"], record["line"])
            self.assertNotIn(key, seen)
            seen.add(key)
            self.assertIn(record["type"], self.manifest["types"])
            if record["type"] not in line_counts:
                line_counts[record["type"]] = [json.loads(l) for l in
                                               (FIXTURES / f"{record['type']}.jsonl").read_text().splitlines()]
            lines = line_counts[record["type"]]
            self.assertLess(record["line"], len(lines), key)
            fixture = lines[record["line"]]
            self.assertEqual(fixture["name"], record["name"], key)
            self.assertFalse(fixture.get("reject"), key)

    def test_fields_are_hex_of_the_right_size(self):
        for record in self.records:
            where = f"{record['type']}#{record['line']}"
            for signature in record["sigs"]:
                self.assertEqual(set(signature), {"sig", "public", "msg"}, where)
                self.assertRegex(signature["sig"], HEX, where)
                # ED25519: a 64-byte signature and a 32-byte key; SECP256K1: 65 and 64 bytes
                self.assertIn((len(signature["sig"]), len(signature["public"])), {(128, 64), (130, 128)}, where)
                self.assertRegex(signature["public"], HEX, where)
                self.assertRegex(signature["msg"], HEX, where)
            for signer in record["signers"]:
                self.assertRegex(signer, HEX, where)
                self.assertEqual(len(signer), 64, where)

    def test_secp256k1_signatures_verify_in_python(self):
        checked = set()
        for record in self.records:
            for signature in record["sigs"]:
                if len(signature["sig"]) != 130 or signature["sig"] in checked:
                    continue
                checked.add(signature["sig"])
                sig, key = bytes.fromhex(signature["sig"]), bytes.fromhex(signature["public"])
                public = (int.from_bytes(key[:32], "big"), int.from_bytes(key[32:], "big"))
                self.assertTrue(secp_reference.verify(
                    public, bytes.fromhex(signature["msg"]),
                    int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:64], "big")), record["name"])
        self.assertGreater(len(checked), 100)

    def test_records_cover_the_signed_types(self):
        signed = {r["type"] for r in self.records if r["sigs"] or r["signers"]}
        for required in ["SignedTransaction", "BlockHeader", "ShardChunkHeader", "Approval", "Block", "ChunkEndorsement",
                         "PartialEncodedStateWitness", "SignedDelegateAction", "SpiceChunkEndorsement"]:
            self.assertIn(required, signed)
        self.assertLess(SIGNATURES.stat().st_size, 5 * 1024 * 1024)


if __name__ == "__main__":
    unittest.main()
