import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "umbrella_imports", Path(__file__).resolve().parents[1] / "check_umbrella_imports.py")
umbrella = importlib.util.module_from_spec(spec)
spec.loader.exec_module(umbrella)


class UmbrellaImportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.write("near-lean/vm/NearVM.lean", "import NearVM.Run\nimport NearVM.Proofs\n")
        self.write("near-lean/vm/tests/Main.lean", "import NearVM.Run\n")

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def test_precise_imports_pass(self):
        self.assertEqual(umbrella.check(self.root), [])

    def test_umbrella_import_fails(self):
        self.write("near-lean/vm/tests/Main.lean", "import NearVM.Run\npublic import NearVM\n")
        self.assertEqual(umbrella.check(self.root), [
            "near-lean/vm/tests/Main.lean:2: imports the umbrella `NearVM`; import the modules it uses"])

    def test_submodule_with_umbrella_prefix_passes(self):
        self.write("contracts/c/verification/Model.lean", "import NearRuntime.Boundary\nimport Wasm.Bytes\n")
        self.assertEqual(umbrella.check(self.root), [])


if __name__ == "__main__":
    unittest.main()
