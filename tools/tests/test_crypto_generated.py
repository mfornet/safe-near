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

    def test_sha2_rounds_are_up_to_date(self):
        committed = (CRYPTO / "NearCrypto/Sha2Rounds.lean").read_text()
        self.assertEqual(tokens(generated("gen_sha.py")), tokens(committed))


if __name__ == "__main__":
    unittest.main()
