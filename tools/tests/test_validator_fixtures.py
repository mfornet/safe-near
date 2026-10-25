"""The validator oracle fixtures (`tools/node-conformance/src/validator_*.rs`)."""
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "near-lean/node/fixtures/validator"
HEX = re.compile(r"^([0-9a-f]{2})*$")


def lines(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


class Fixtures(unittest.TestCase):
    def test_manifest_matches_files(self):
        manifest = json.loads((FIXTURES / "manifest.json").read_text())
        reference = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())
        self.assertEqual(manifest["protocol_version"], reference["reference_protocol_version"])
        for name, count in manifest["lines"].items():
            self.assertEqual(len(lines(FIXTURES / f"{name}.jsonl")), count, name)
        # every file but the zstd frames (written by the node) is in the manifest
        files = {p.stem for p in FIXTURES.glob("*.jsonl")} - {"zstd-stored"}
        self.assertEqual(files, set(manifest["lines"]))

    def test_hex_fields_are_hex(self):
        for path in FIXTURES.glob("*.jsonl"):
            for row in lines(path):
                for key, value in row.items():
                    if isinstance(value, str) and key not in {"account", "secret", "ratio", "error", "case", "name"}:
                        if key in {"minGasPrice", "maxGasPrice"}:
                            continue
                        self.assertRegex(value, HEX, f"{path.name}:{key}")

    def test_chunks_use_the_protocol_header(self):
        for row in lines(FIXTURES / "chunk.jsonl"):
            self.assertEqual(row["protocol"], 86)

    def test_zstd_frames_start_with_the_magic(self):
        for row in lines(FIXTURES / "zstd-stored.jsonl"):
            self.assertTrue(row["frame"].startswith("28b52ffd"))
            self.assertLessEqual(len(row["input"]), len(row["frame"]))


if __name__ == "__main__":
    unittest.main()
