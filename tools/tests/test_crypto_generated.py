from pathlib import Path
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
CRYPTO = ROOT / "near-lean/crypto"


def tokens(text):
    return re.sub(r"\s+", "", text)


def generated(script):
    return subprocess.run([sys.executable, str(CRYPTO / "scripts" / script)], check=True,
                          stdout=subprocess.PIPE, text=True).stdout


class GeneratedSourceTests(unittest.TestCase):
    """Each generated Lean file is what its script writes, up to the formatter's whitespace."""

    def test_fe_mul_is_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/Ed25519/FeMul.lean").read_text()
        self.assertEqual(tokens(generated("gen_fe.py")), tokens(committed))

    def test_fp_mul_is_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/Secp256k1/FpMul.lean").read_text()
        self.assertEqual(tokens(generated("gen_fp.py")), tokens(committed))

    def test_blake2b_rounds_are_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/Blake2bRounds.lean").read_text()
        self.assertEqual(tokens(generated("gen_blake2b.py")), tokens(committed))

    def test_point_ops_are_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/Secp256k1/PointOps.lean").read_text()
        self.assertEqual(tokens(generated("gen_point_ops.py")), tokens(committed))

    def test_mod_inv_is_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/ModInv.lean").read_text()
        self.assertEqual(tokens(generated("gen_modinv.py")), tokens(committed))

    def test_sha2_rounds_are_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/Sha2Rounds.lean").read_text()
        self.assertEqual(tokens(generated("gen_sha.py")), tokens(committed))


BLST_SOURCES = sorted(Path.home().glob(".cargo/registry/src/*/blst-0.3.11/blst/src"))


@unittest.skipUnless(BLST_SOURCES, "blst 0.3.11 is not in the cargo registry")
class BlstConstantsTests(unittest.TestCase):
    """The hash-to-curve constants are what `gen_bls_isogeny.py` reads out of blst's sources (the
    isogeny property of the committed numbers is checked by `test_bls_isogeny.py` everywhere)."""

    def test_isogeny_constants_are_up_to_date(self):
        out = subprocess.run([sys.executable, str(CRYPTO / "scripts" / "gen_bls_isogeny.py"),
                              str(BLST_SOURCES[0])], check=True, stdout=subprocess.PIPE, text=True).stdout
        committed = (CRYPTO / "NearCrypto/Bls12381/Isogeny.lean").read_text()
        self.assertEqual(tokens(out), tokens(committed))


if __name__ == "__main__":
    unittest.main()
