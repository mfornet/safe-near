import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "near-lean/node/fixtures/types"
HEX = re.compile(r"^(?:[0-9a-f]{2})*$")
LIMIT = 12 * 1024 * 1024


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


if __name__ == "__main__":
    unittest.main()
