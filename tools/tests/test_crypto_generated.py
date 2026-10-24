from pathlib import Path
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
CRYPTO = ROOT / "near-lean/crypto"


def tokens(text):
    return re.sub(r"\s+", "", text)


class GeneratedFieldTests(unittest.TestCase):
    """`FeMul.lean` is what `scripts/gen_fe.py` writes, up to the formatter's whitespace."""

    def test_fe_mul_is_up_to_date(self):
        generated = subprocess.run([sys.executable, str(CRYPTO / "scripts/gen_fe.py")], check=True,
                                   stdout=subprocess.PIPE, text=True).stdout
        committed = (CRYPTO / "NearCrypto/Ed25519/FeMul.lean").read_text()
        self.assertEqual(tokens(generated), tokens(committed))


if __name__ == "__main__":
    unittest.main()
