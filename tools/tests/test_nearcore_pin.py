import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
spec = importlib.util.spec_from_file_location("nearcore_pin", TOOLS / "check_nearcore_pin.py")
nearcore_pin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(nearcore_pin)
PIN = "a" * 40
OTHER = "b" * 40
WORKFLOW = """\
      - uses: actions/checkout@v5
        with:
          repository: near/nearcore
          ref: {ref}
          path: reference-nearcore
"""


class NearcorePinTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.write("near-lean/runtime/reference.json", json.dumps({"revision": PIN}))

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def test_matching_pins(self):
        self.write(".github/workflows/ref.yml", WORKFLOW.format(ref=PIN))
        self.write("tools/runtime-finance-reference/build.py", f'PIN = "{PIN}"\n')
        self.write("notes/a.md", f"https://github.com/near/nearcore/blob/{PIN}/x.rs\n")
        self.assertEqual(nearcore_pin.check(self.root), [])

    def test_stale_workflow_checkout(self):
        self.write(".github/workflows/ref.yml", WORKFLOW.format(ref=OTHER))
        self.assertIn(".github/workflows/ref.yml:4:", "\n".join(nearcore_pin.check(self.root)))

    def test_stale_adapter_literal(self):
        self.write("tools/runtime-nonce-reference/compare.py", f'assert rev == "{OTHER}"\n')
        self.assertIn("compare.py:1:", "\n".join(nearcore_pin.check(self.root)))

    def test_stale_source_link(self):
        self.write("notes/a.md", f"https://github.com/near/nearcore/tree/{OTHER}\n")
        self.assertEqual(len(nearcore_pin.check(self.root)), 1)

    def test_other_repositories_are_ignored(self):
        self.write("contracts/x/oracle.py", f'PIN = "{OTHER}"\n')
        self.write(".github/workflows/other.yml", WORKFLOW.replace("near/nearcore", "near/near-sdk-rs")
                   .format(ref=OTHER))
        self.assertEqual(nearcore_pin.check(self.root), [])

    def test_reports_are_ignored(self):
        self.write("reports/old.md", f"https://github.com/near/nearcore/blob/{OTHER}/x.rs\n")
        self.assertEqual(nearcore_pin.check(self.root), [])


if __name__ == "__main__":
    unittest.main()
