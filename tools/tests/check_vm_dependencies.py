"""Lean fixture regressions for check_vm_dependencies.py; needs `lake` (see tools/README.md)."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_vm_dependencies as dependencies


class VMDependencyFixtureTests(unittest.TestCase):
    def test_compiler_detects_transitive_legacy_imports_and_missing_execution(self):
        with tempfile.TemporaryDirectory(prefix="safe-near-vm-deps-test-") as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text((dependencies.ROOT / "lean-toolchain").read_text())
            (root / "lakefile.toml").write_text(
                'name = "VMDependencyFixture"\n[[lean_lib]]\nname = "NearVM"\n'
                '[[lean_lib]]\nname = "Wasm"\n[[lean_lib]]\nname = "Interpreter"\n')
            wasm = root / "Wasm"
            wasm.mkdir(parents=True)
            (wasm / "Validate.lean").write_text('def validateValue : Nat := 1\n')
            (wasm / "Link.lean").write_text('def linkValue : Nat := 1\n')
            (wasm / "Exec.lean").write_text('import Wasm.Validate\nimport Wasm.Link\n')
            (root / "NearVM.lean").write_text('import Wasm.Exec\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            report = root / "dependencies.json"
            result = dependencies.audit(root, report)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(report.read_text())["forbidden"], [])

            # The root source never mentions the forbidden module. Only the
            # compiler's transitive header exposes this indirect dependency.
            legacy = root / "Interpreter/Wasm"
            legacy.mkdir(parents=True)
            (legacy / "Semantics.lean").write_text('def legacyValue : Nat := 2\n')
            (wasm / "Bridge.lean").write_text('import Interpreter.Wasm.Semantics\n')
            (wasm / "Exec.lean").write_text(
                'import Wasm.Validate\nimport Wasm.Link\nimport Wasm.Bridge\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            result = dependencies.audit(root, report)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads(report.read_text())["forbidden"], ["Interpreter.Wasm.Semantics"])
            self.assertIn("legacy interpreter", result.stdout)

            # Node-side packages are forbidden the same way.
            (root / "lakefile.toml").write_text(
                (root / "lakefile.toml").read_text() + '[[lean_lib]]\nname = "NearChain"\n')
            (root / "NearChain.lean").write_text('def chainValue : Nat := 4\n')
            (wasm / "Bridge.lean").write_text('import NearChain\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            result = dependencies.audit(root, report)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads(report.read_text())["forbidden"], ["NearChain"])
            self.assertIn("node packages", result.stdout)

            (root / "NearVM.lean").write_text('def disconnected : Nat := 3\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            result = dependencies.audit(root, report)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Wasm.Exec", json.loads(report.read_text())["missing"])


if __name__ == "__main__":
    unittest.main()
