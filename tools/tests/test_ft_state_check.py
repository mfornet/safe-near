"""ft_state_check.py and the Lean ft-state-check on real (corpus) and tampered storage."""

import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ft_state_check as ft  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
CHUNK = ROOT / "near-lean/chain/corpus/chunks/sharded-h00000066-s3"


@unittest.skipUnless(ft.BINARY.exists(), "ft-state-check is not built")
class FtStateCheck(unittest.TestCase):
    def storage(self):
        storage = ft.chunk_storage(CHUNK, "ft.node0")
        self.assertTrue(storage)
        return storage

    def test_corpus_token_holds(self):
        result = ft.check(self.storage())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("invariant holds", result.stdout)

    def test_inflated_balance_is_a_violation(self):
        storage = self.storage()
        for row in storage:
            if bytes.fromhex(row[0]).startswith(b"\x00"):
                row[1] = (int.from_bytes(bytes.fromhex(row[1]), "little") + 1).to_bytes(16, "little").hex()
                break
        result = ft.check(storage)
        self.assertEqual(result.returncode, 1)
        self.assertIn("balances sum to", result.stdout)

    def test_malformed_balance_does_not_decode(self):
        storage = self.storage()
        for row in storage:
            if bytes.fromhex(row[0]).startswith(b"\x00"):
                row[1] = row[1][:-2]
                break
        self.assertEqual(ft.check(storage).returncode, 2)

    def test_missing_state_does_not_decode(self):
        storage = [row for row in self.storage() if bytes.fromhex(row[0]) != b"STATE"]
        self.assertEqual(ft.check(storage).returncode, 2)


if __name__ == "__main__":
    unittest.main()
