import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "toolchains", Path(__file__).resolve().parents[1] / "check_lean_toolchains.py")
toolchains = importlib.util.module_from_spec(spec)
spec.loader.exec_module(toolchains)
PIN = "leanprover/lean4:v4.34.1\n"


class ToolchainTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.write("lean-toolchain", PIN)
        self.write("pkg/lakefile.toml", 'name = "Example"\n')
        self.write("pkg/lean-toolchain", PIN)

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def test_matching_pins(self):
        self.assertEqual(toolchains.check(self.root), [])

    def test_mismatched_new_package(self):
        self.write("new/lakefile.lean", "import Lake\n")
        self.write("new/lean-toolchain", "leanprover/lean4:v4.33.0\n")
        self.assertIn("new/lean-toolchain: expected", "\n".join(toolchains.check(self.root)))

    def test_missing_pin(self):
        (self.root / "pkg/lean-toolchain").unlink()
        self.assertIn("missing toolchain pin", "\n".join(toolchains.check(self.root)))

    def test_rejects_unpinned_canonical_version(self):
        self.write("lean-toolchain", "leanprover/lean4:stable\n")
        self.assertIn("must pin a Lean release", toolchains.check(self.root)[0])

    def test_ignored_build_packages_are_excluded(self):
        self.write(".gitignore", ".lake/\n")
        self.write(".lake/packages/dependency/lakefile.toml", 'name = "Dependency"\n')
        self.assertEqual(toolchains.check(self.root), [])

    def test_submodule_contents_are_excluded(self):
        child = self.root / "vendor"
        subprocess.run(["git", "init", "-q", str(child)], check=True)
        self.write("vendor/lakefile.toml", 'name = "Upstream"\n')
        subprocess.run(["git", "add", "lakefile.toml"], cwd=child, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.com",
                        "commit", "-qm", "fixture"], cwd=child, check=True)
        subprocess.run(["git", "add", "vendor"], cwd=self.root, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(toolchains.check(self.root), [])

    def test_changed_files_include_new_sources_but_not_ignored_or_deleted_ones(self):
        self.write(".gitignore", ".lake/\n")
        self.write("pkg/Edited.lean", "def old := 1\n")
        self.write("pkg/Deleted.lean", "def deleted := 1\n")
        subprocess.run(["git", "add", "."], cwd=self.root, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.com",
                        "commit", "-qm", "fixture"], cwd=self.root, check=True)
        self.write("pkg/Edited.lean", "def changed := 2\n")
        (self.root / "pkg/Deleted.lean").unlink()
        self.write("pkg/New.lean", "def new := 3\n")
        self.write("pkg/Staged.lean", "def staged := 4\n")
        subprocess.run(["git", "add", "pkg/Staged.lean"], cwd=self.root, check=True)
        self.write(".lake/Ignored.lean", "def ignored := 5\n")
        self.assertEqual(toolchains.changed_files(self.root, "HEAD"), {
            Path("pkg/Edited.lean"), Path("pkg/New.lean"), Path("pkg/Staged.lean"),
        })


if __name__ == "__main__":
    unittest.main()
