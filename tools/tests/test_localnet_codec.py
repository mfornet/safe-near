"""Localnet transaction construction: Ed25519, base58, Borsh layouts and the generated wasm (no neard)."""
import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "localnet"))
import nearcodec as nc  # noqa: E402
import wasmgen  # noqa: E402

RFC8032 = [  # seed, public key, message, signature (RFC 8032, section 7.1)
    ("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
     "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a", "",
     "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
     "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"),
    ("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
     "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c", "72",
     "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da"
     "085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"),
]


class Ed25519(unittest.TestCase):
    def test_rfc_vectors(self):
        for seed, public, message, signature in RFC8032:
            seed, message = bytes.fromhex(seed), bytes.fromhex(message)
            self.assertEqual(nc.ed25519_public(seed).hex(), public)
            self.assertEqual(nc.ed25519_sign(seed, message).hex(), signature)
            self.assertTrue(nc.ed25519_verify(bytes.fromhex(public), message, bytes.fromhex(signature)))

    def test_rejects_tampering(self):
        key = nc.Key.derive("test")
        signature = nc.ed25519_sign(key.seed, b"message")
        self.assertFalse(nc.ed25519_verify(key.public, b"messagE", signature))
        self.assertFalse(nc.ed25519_verify(key.public, b"message", signature[:-1] + bytes([signature[-1] ^ 1])))


class Encoding(unittest.TestCase):
    def test_base58_round_trip(self):
        for data in [b"", b"\0", b"\0\0abc", bytes(range(32)), b"\xff" * 32]:
            self.assertEqual(nc.b58decode(nc.b58encode(data)), data)
        self.assertEqual(nc.b58encode(bytes(32)), "1" * 32)

    def test_borsh_layouts(self):
        self.assertEqual(nc.string("ab"), b"\x02\0\0\0ab")
        self.assertEqual(nc.u128(1), b"\x01" + bytes(15))
        self.assertEqual(nc.transfer(5), b"\x03\x05" + bytes(15))
        self.assertEqual(nc.create_account(), b"\x00")
        self.assertEqual(nc.deploy_contract(b"xy"), b"\x01\x02\0\0\0xy")
        self.assertEqual(nc.function_call("m", b"a", 7, 9),
                         b"\x02" + nc.string("m") + nc.blob(b"a") + nc.u64(7) + nc.u128(9))
        self.assertEqual(nc.access_key_full(3), nc.u64(3) + b"\x01")
        self.assertEqual(nc.use_global_contract_by_hash(bytes(32)), b"\x0a\x00" + bytes(32))

    def test_transaction_signature_covers_the_body(self):
        key = nc.Key.derive("signer")
        raw = nc.transaction("alice.near", key, 7, "bob.near", bytes(32), [nc.transfer(1)])
        body, signature = raw[:-65], raw[-65:]
        self.assertEqual(signature[0], 0)
        self.assertTrue(nc.ed25519_verify(key.public, hashlib.sha256(body).digest(), signature[1:]))
        self.assertEqual(nc.transaction_hash(raw), hashlib.sha256(body).digest())
        self.assertEqual(body[:4], (10).to_bytes(4, "little"))     # signer id length starts a V0 transaction

    def test_strict_transaction_is_tagged_v1(self):
        key = nc.Key.derive("signer")
        raw = nc.transaction_v1_strict("alice.near", key, 1, "bob.near", bytes(32), [])
        self.assertEqual(raw[0], 1)

    def test_derived_keys_are_deterministic_and_distinct(self):
        self.assertEqual(nc.Key.derive("x").public, nc.Key.derive("x").public)
        self.assertNotEqual(nc.Key.derive("x").public, nc.Key.derive("y").public)


class GeneratedWasm(unittest.TestCase):
    def test_modules_have_the_expected_exports(self):
        for module, names in [(wasmgen.hostcalls(), [b"ecrecover_once", b"ed25519_once", b"p256_once"]),
                              (wasmgen.noop_contract(), [b"noop"])]:
            self.assertEqual(module[:8], b"\0asm\x01\0\0\0")
            for name in names:
                self.assertIn(name, module)

    def test_generation_is_deterministic(self):
        self.assertEqual(wasmgen.hostcalls(), wasmgen.hostcalls())


if __name__ == "__main__":
    unittest.main()
