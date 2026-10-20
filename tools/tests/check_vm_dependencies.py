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
                '[[lean_lib]]\nname = "Interpreter"\n')
            wasm = root / "Interpreter/Wasm"
            wasm.mkdir(parents=True)
            (wasm / "Operations.lean").write_text('def operationValue : Nat := 1\n')
            (wasm / "SmallStep.lean").write_text('import Interpreter.Wasm.Operations\n')
            (root / "NearVM.lean").write_text('import Interpreter.Wasm.SmallStep\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            report = root / "dependencies.json"
            result = dependencies.audit(root, report)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(report.read_text())["forbidden"], [])

            # The root source never mentions the forbidden module. Only the
            # compiler's transitive header exposes this indirect dependency.
            (wasm / "Semantics.lean").write_text('def legacyValue : Nat := 2\n')
            (wasm / "Bridge.lean").write_text('import Interpreter.Wasm.Semantics\n')
            (wasm / "SmallStep.lean").write_text(
                'import Interpreter.Wasm.Operations\nimport Interpreter.Wasm.Bridge\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            result = dependencies.audit(root, report)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads(report.read_text())["forbidden"], ["Interpreter.Wasm.Semantics"])
            self.assertIn("legacy interpreter", result.stdout)

            (root / "NearVM.lean").write_text('def disconnected : Nat := 3\n')
            subprocess.run(["lake", "build", "NearVM"], cwd=root, check=True, capture_output=True)
            result = dependencies.audit(root, report)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Interpreter.Wasm.SmallStep", json.loads(report.read_text())["missing"])


if __name__ == "__main__":
    unittest.main()
