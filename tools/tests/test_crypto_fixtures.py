import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "near-lean/crypto/fixtures"
HEX = re.compile(r"^(?:[0-9a-f]{2})*$")
LIMIT = 5 * 1024 * 1024
DIGEST_BYTES = {"sha256": 32, "sha512": 64, "keccak256": 32, "keccak512": 64, "ripemd160": 20,
                "blake2b256": 32, "blake2b512": 64}
P = 2**256 - 2**32 - 977
N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
G = (0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
     0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)


def ec_add(a, b):
    """Affine addition on secp256k1; None is infinity."""
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        m = 3 * a[0] * a[0] * pow(2 * a[1], -1, P) % P
    else:
        m = (b[1] - a[1]) * pow(b[0] - a[0], -1, P) % P
    x = (m * m - a[0] - b[0]) % P
    return x, (m * (a[0] - x) - a[1]) % P


def ec_mul(k, point):
    result = None
    while k:
        if k & 1:
            result = ec_add(result, point)
        point = ec_add(point, point)
        k >>= 1
    return result
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
        cls.secp = lines("secp256k1.jsonl")
        cls.vrf = lines("vrf.jsonl")

    def test_size(self):
        self.assertLess(sum(p.stat().st_size for p in FIXTURES.iterdir()), LIMIT)

    def test_counts_match_manifest(self):
        for name, records in (("hash.jsonl", self.hashes), ("ed25519.jsonl", self.ed25519),
                              ("secp256k1.jsonl", self.secp), ("vrf.jsonl", self.vrf)):
            counts = {}
            for record in records:
                kind = record.get("kind", "hash")
                counts[kind] = counts.get(kind, 0) + 1
            self.assertEqual(counts, self.manifest["files"][name], name)
        self.assertEqual(set(self.manifest["files"]),
                         {"hash.jsonl", "ed25519.jsonl", "secp256k1.jsonl", "vrf.jsonl"})

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

    def test_digests_against_hashlib(self):
        for record in self.hashes:
            if record["alg"] not in ("sha256", "sha512", "blake2b256", "blake2b512"):
                continue
            if "msg" in record:
                message = bytes.fromhex(record["msg"])
            else:
                message = bytes.fromhex(record["unit"]) * record["count"]
            if record["alg"].startswith("blake2b"):
                digest = hashlib.blake2b(message, digest_size=DIGEST_BYTES[record["alg"]]).hexdigest()
            else:
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

    def test_secp256k1_keys_against_python_arithmetic(self):
        count = 0
        for record in self.secp:
            if record["kind"] != "keypair":
                continue
            point = ec_mul(int(record["secret"], 16), G)
            self.assertEqual(record["public"], f"{point[0]:064x}{point[1]:064x}", record["name"])
            self.assertEqual(record["compressed"], f"{2 + (point[1] & 1):02x}{point[0]:064x}", record["name"])
            count += 1
        self.assertGreater(count, 40)

    def test_secp256k1_signatures_against_python_arithmetic(self):
        recids = set()
        for record in self.secp:
            if record["kind"] != "sign":
                continue
            sig = bytes.fromhex(record["sig"])
            r, s, v = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:64], "big"), sig[64]
            m = int(record["msg"], 16) % N
            public = (int(record["public"][:64], 16), int(record["public"][64:], 16))
            self.assertEqual(ec_mul(int(record["secret"], 16), G), public, record["name"])
            self.assertTrue(0 < r < N and 0 < s <= (N - 1) // 2, record["name"])
            w = pow(s, -1, N)
            point = ec_add(ec_mul(m * w % N, G), ec_mul(r * w % N, public))
            self.assertEqual(point[0] % N, r, record["name"])
            # the recovery id: bit 0 is the parity of R.y (R = the point, before s was made low)
            self.assertEqual(v & 1, point[1] & 1, record["name"])
            self.assertLess(v, 4)
            recids.add(v)
        self.assertGreaterEqual(recids, {0, 1})

    def test_secp256k1_recoveries_against_python_arithmetic(self):
        recovered = 0
        for record in self.secp:
            if record["kind"] != "recover" or not record["valid"]:
                continue
            sig = bytes.fromhex(record["sig"])
            r, s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
            v, m = record["v"], int(record["msg"], 16) % N
            self.assertTrue(0 < r < N and 0 < s < N and 0 <= v < 4, record["name"])
            x = r + N if v >= 2 else r
            self.assertLess(x, P, record["name"])
            y = pow((x**3 + 7) % P, (P + 1) // 4, P)
            self.assertEqual(y * y % P, (x**3 + 7) % P, record["name"])
            if y & 1 != v & 1:
                y = P - y
            rinv = pow(r, -1, N)
            q = ec_add(ec_mul(s * rinv % N, (x, y)), ec_mul((N - m * rinv) % N, G))
            self.assertEqual(record["public"], f"{q[0]:064x}{q[1]:064x}", record["name"])
            recovered += 1
        self.assertGreater(recovered, 400)

    def test_secp256k1_pubkey_lines(self):
        verdicts = set()
        for record in self.secp:
            if record["kind"] != "pubkey":
                continue
            verdicts.add(record["valid"])
            if record["valid"]:
                x, y = int(record["public"][:64], 16), int(record["public"][64:], 16)
                self.assertEqual(y * y % P, (x**3 + 7) % P, record["name"])
                self.assertEqual(record["compressed"], f"{2 + (y & 1):02x}{x:064x}", record["name"])
        self.assertEqual(verdicts, {True, False})

    def test_secp256k1_structure(self):
        kinds = {"secret", "keypair", "sign", "pubkey", "recover", "verify", "ecrecover"}
        for number, record in enumerate(self.secp, 1):
            where = f"secp256k1.jsonl:{number}"
            self.assertIn(record["kind"], kinds, where)
            for key, value in record.items():
                if key in ("kind", "name", "valid", "v", "malleability"):
                    continue
                self.assertRegex(value, HEX, f"{where} {key}")
            if record["kind"] in ("verify", "recover", "ecrecover", "pubkey"):
                self.assertIsInstance(record["valid"], bool, where)
        for kind in ("verify", "recover", "ecrecover", "pubkey", "secret"):
            self.assertEqual({r["valid"] for r in self.secp if r["kind"] == kind}, {True, False}, kind)
        for flag in (0, 1):
            self.assertTrue(any(r["kind"] == "ecrecover" and r["malleability"] == flag and r["valid"] for r in self.secp))
        # high s: valid for recovery without the flag and invalid with it
        by_name = {}
        for r in self.secp:
            if r["kind"] == "ecrecover":
                by_name.setdefault((r["name"], r["v"]), {})[r["malleability"]] = r["valid"]
        self.assertTrue(any(v.get(0) and v.get(1) is False for v in by_name.values()))

    def test_vrf_structure(self):
        kinds = {"ristretto", "basemul", "vmul2", "key", "convert", "compute", "vrf-public", "vrf-secret",
                 "verify", "block"}
        for number, record in enumerate(self.vrf, 1):
            where = f"vrf.jsonl:{number}"
            self.assertIn(record["kind"], kinds, where)
            for key, value in record.items():
                if key in ("kind", "name", "valid"):
                    continue
                self.assertRegex(value, HEX, f"{where} {key}")
                if key in ("value", "secret", "public", "ed25519", "point", "bytes", "double", "scalar"):
                    self.assertEqual(len(value), 64, f"{where} {key}")
                if key == "proof":
                    self.assertEqual(len(value), 128, f"{where} {key}")
        for kind in ("ristretto", "convert", "verify", "vrf-public", "vrf-secret"):
            self.assertEqual({r["valid"] for r in self.vrf if r["kind"] == kind}, {True, False}, kind)

    def test_vrf_block_random_value_is_sha256_of_value(self):
        blocks = [r for r in self.vrf if r["kind"] == "block"]
        self.assertGreater(len(blocks), 5)
        for record in blocks:
            self.assertEqual(hashlib.sha256(bytes.fromhex(record["value"])).hexdigest(), record["random"])


if __name__ == "__main__":
    unittest.main()
