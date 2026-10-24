import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "near-lean/crypto/fixtures"
HEX = re.compile(r"^(?:[0-9a-f]{2})*$")
LIMIT = 5 * 1024 * 1024
DIGEST_BYTES = {"sha256": 32, "sha512": 64, "keccak256": 32, "keccak512": 64, "ripemd160": 20}
FIELD_BYTES = {"seed": 32, "public": 32, "keypair": 64, "sig": 64}
KINDS = {"keypair", "keypair-check", "sign", "verify", "pubkey"}


def lines(name):
    return [json.loads(line) for line in (FIXTURES / name).read_text().splitlines()]


class CryptoFixtureTests(unittest.TestCase):
    """The committed crypto fixtures are well formed and consistent with the manifest."""

    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((FIXTURES / "manifest.json").read_text())
        cls.hashes = lines("hash.jsonl")
        cls.ed25519 = lines("ed25519.jsonl")

    def test_size(self):
        self.assertLess(sum(p.stat().st_size for p in FIXTURES.iterdir()), LIMIT)

    def test_counts_match_manifest(self):
        for name, records in (("hash.jsonl", self.hashes), ("ed25519.jsonl", self.ed25519)):
            counts = {}
            for record in records:
                kind = record.get("kind", "hash")
                counts[kind] = counts.get(kind, 0) + 1
            self.assertEqual(counts, self.manifest["files"][name], name)
        self.assertEqual(set(self.manifest["files"]), {"hash.jsonl", "ed25519.jsonl"})

    def test_hash_lines(self):
        seen = set()
        for number, record in enumerate(self.hashes, 1):
            where = f"hash.jsonl:{number}"
            self.assertEqual(set(record) - {"msg", "unit", "count"}, {"alg", "name", "digest"}, where)
            self.assertIn(record["alg"], DIGEST_BYTES, where)
            self.assertNotIn((record["alg"], record["name"]), seen, where)
            seen.add((record["alg"], record["name"]))
            self.assertRegex(record["digest"], HEX, where)
            self.assertEqual(len(record["digest"]), 2 * DIGEST_BYTES[record["alg"]], where)
            if "msg" in record:
                self.assertRegex(record["msg"], HEX, where)
            else:
                self.assertRegex(record["unit"], HEX, where)
                self.assertGreater(record["count"], 0, where)
        for alg in DIGEST_BYTES:
            names = {n for a, n in seen if a == alg}
            for required in ["random-0", "random-55", "random-56", "random-64", "random-111", "random-112",
                             "random-128", "random-136", "random-137", "million-a", "abc"]:
                self.assertIn(required, names, alg)

    def test_sha2_digests_against_hashlib(self):
        for record in self.hashes:
            if record["alg"] not in ("sha256", "sha512"):
                continue
            if "msg" in record:
                message = bytes.fromhex(record["msg"])
            else:
                message = bytes.fromhex(record["unit"]) * record["count"]
            digest = hashlib.new(record["alg"], message).hexdigest()
            self.assertEqual(digest, record["digest"], record["name"])

    def test_ed25519_lines(self):
        verdicts = {"verify": set(), "pubkey": set(), "keypair-check": set()}
        seen = set()
        for number, record in enumerate(self.ed25519, 1):
            where = f"ed25519.jsonl:{number}"
            self.assertIn(record["kind"], KINDS, where)
            self.assertNotIn((record["kind"], record["name"], record.get("sig"), record.get("public")), seen, where)
            seen.add((record["kind"], record["name"], record.get("sig"), record.get("public")))
            for key, value in record.items():
                if key in ("kind", "name", "valid"):
                    continue
                self.assertRegex(value, HEX, f"{where} {key}")
                if key in FIELD_BYTES:
                    self.assertEqual(len(value), 2 * FIELD_BYTES[key], f"{where} {key}")
            if record["kind"] in verdicts:
                self.assertIsInstance(record["valid"], bool, where)
                verdicts[record["kind"]].add(record["valid"])
        for kind, values in verdicts.items():
            self.assertEqual(values, {True, False}, f"{kind} needs accepts and rejects")

    def test_ed25519_edge_cases_present(self):
        names = {r["name"] for r in self.ed25519 if r["kind"] == "verify"}
        for prefix in ("zip215/A0-R0", "zip215/A13-R13", "mixed-order/T1-accept", "mixed-order/T1-reject",
                       "scalar/ell", "key0/S-plus-1-ell", "key0/R-bit-255", "identity/any-message-0"):
            self.assertIn(prefix, names)
        self.assertEqual(sum(n.startswith("zip215/") for n in names), 196)

    def test_rfc8032_vector_one(self):
        record = next(r for r in self.ed25519 if r["kind"] == "sign" and r["name"] == "rfc8032-1-empty")
        self.assertEqual(record["public"], "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
        self.assertEqual(record["sig"], "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")

    def test_keypair_layout(self):
        for record in self.ed25519:
            if record["kind"] == "keypair":
                self.assertEqual(record["keypair"], record["seed"] + record["public"], record["name"])


if __name__ == "__main__":
    unittest.main()
