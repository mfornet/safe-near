import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_format


class FormatSelectionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True)
        self.pin = {"generated": ["pkg/Generated/*.lean"]}
        self.write("pkg/lakefile.toml", 'name = "Example"\n')
        self.write("pkg/Source.lean", "def value := 1\n")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_closest_nested_package_owns_each_file(self):
        self.write("pkg/nested/lakefile.lean", "import Lake\n")
        self.write("pkg/nested/Inner.lean", "def inner := 0\n")
        groups, _ = lean_format.source_groups(self.root, [], self.pin)
        self.assertEqual(groups[Path("pkg")], [Path("Source.lean")])
        self.assertIn(Path("Inner.lean"), groups[Path("pkg/nested")])

    def test_generated_sources_are_protected(self):
        self.write("pkg/Generated/Program.lean", "def generated := 1\n")
        groups, skipped = lean_format.source_groups(self.root, [], self.pin)
        self.assertEqual(groups, {Path("pkg"): [Path("Source.lean")]})
        self.assertEqual(len(skipped), 1)
        for path in skipped:
            with self.assertRaisesRegex(ValueError, "protected"):
                lean_format.source_groups(self.root, [path], self.pin)

    def test_explicit_unknown_or_outside_file_is_rejected(self):
        for path in [Path("../outside.lean"), Path("/tmp/outside.lean"), Path("missing.lean")]:
            with self.assertRaises(ValueError):
                lean_format.source_groups(self.root, [path], self.pin)

    def test_standalone_script_is_explicitly_outside_package_scope(self):
        self.write("tools/Driver.lean", "import Lean\n")
        with self.assertRaisesRegex(ValueError, "outside a Lake package"):
            lean_format.source_groups(self.root, [Path("tools/Driver.lean")], self.pin)

    def test_ignored_dependencies_do_not_enter_selection(self):
        self.write(".gitignore", ".lake/\n")
        self.write("pkg/.lake/packages/upstream/Bad.lean", "def upstream := 1\n")
        _, skipped = lean_format.source_groups(self.root, [], self.pin)
        self.assertEqual(skipped, [])

    def test_killed_formatter_is_a_failure(self):
        with patch.object(lean_format.subprocess, "run", return_value=SimpleNamespace(returncode=-9)):
            self.assertEqual(lean_format.run_groups(
                self.root, {Path("pkg"): [Path("Source.lean")]}, Path("formatter"), {}), 2)


if __name__ == "__main__":
    unittest.main()
