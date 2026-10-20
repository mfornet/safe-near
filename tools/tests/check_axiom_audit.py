"""Real-Lean regression for package-local axiom audit artifact selection."""

import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("axiom_audit", ROOT / "tools/axiom-audit.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class AxiomAuditArtifactTests(unittest.TestCase):
    def test_cli_rejects_missing_or_ambiguous_open_module_policy(self):
        with tempfile.TemporaryDirectory(prefix="safe-near-audit-policy-") as directory:
            report = Path(directory) / "report.json"
            base = ["python3", str(ROOT / "tools/axiom-audit.py"),
                    str(ROOT / "near-lean/programs/lean"), "--report", str(report), "--no-build"]
            for options, message in [
                (["--allow-sorry-module", "Programs.DoesNotExist"], "allowed sorry module is absent"),
                (["--allow-sorry", "--allow-sorry-module", "Programs.Mergesort.Proof"], "cannot be combined"),
            ]:
                with self.subTest(options=options):
                    result = subprocess.run(base + options, cwd=ROOT, text=True, capture_output=True)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn(message, result.stderr)
                    self.assertFalse(report.exists())

    def test_named_open_modules_do_not_exempt_other_modules_or_compiler_axioms(self):
        open_proof = dict(module="Open", declaration="unfinished", axioms=["sorryAx"])
        other = dict(module="Other", declaration="regression", axioms=["sorryAx"])
        native = dict(module="Open", declaration="native", axioms=["Lean.ofReduceBool"])
        violations = [open_proof, other, native]
        self.assertEqual(AUDIT.failing_violations(violations, False, [], ["Open"]), [other, native])
        self.assertEqual(AUDIT.failing_violations(violations, False, ["Open"], ["Open"]), violations)

    def test_completed_modules_cannot_use_the_open_proof_exception(self):
        complete = dict(module="Finished", declaration="finished", axioms=["sorryAx"])
        open_proof = dict(module="Open", declaration="unfinished", axioms=["sorryAx"])
        compiler = dict(module="Open", declaration="native", axioms=["Lean.ofReduceBool"])
        mixed = dict(module="Open", declaration="mixed", axioms=["sorryAx", "custom"])
        violations = [complete, open_proof, compiler, mixed]
        self.assertEqual(AUDIT.failing_violations(violations, True, ["Finished"]),
                         [complete, compiler, mixed])
        self.assertEqual(AUDIT.failing_violations(violations, False, []), violations)
        self.assertEqual(AUDIT.failing_violations(violations, True, []), [compiler, mixed])

    def test_audit_uses_local_module_and_rejects_missing_local_artifact(self):
        with tempfile.TemporaryDirectory(prefix="safe-near-axiom-fixture-") as directory:
            root = Path(directory)
            dependency, package = root / "dependency", root / "package"
            for folder, name, body in (
                (dependency, "Dependency", "def dependencyMarker : Nat := 1\n"),
                (package, "Package", "axiom localAuditSentinel : False\ndef localMarker : Nat := 2\n"),
            ):
                (folder / "Tests").mkdir(parents=True)
                (folder / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
                manifest = f'name = "{name}"\n[[lean_lib]]\nname = "{name}"\nroots = ["Tests.Main"]\n'
                if folder == package:
                    manifest += '\n[[require]]\nname = "Dependency"\npath = "../dependency"\n'
                (folder / "lakefile.toml").write_text(manifest)
                (folder / "Tests/Main.lean").write_text(body)
                subprocess.run(["lake", "build", name], cwd=folder, check=True, capture_output=True)

            # Establish that ordinary lookup really hides the local axiom.
            ordinary_source, ordinary_report = root / "Ordinary.lean", root / "ordinary.json"
            ordinary_source.write_text(AUDIT.audit_source(["Tests.Main"], ordinary_report))
            subprocess.run(["lake", "env", "lean", str(ordinary_source)], cwd=package,
                           check=True, capture_output=True)
            ordinary = json.loads(ordinary_report.read_text())
            self.assertEqual(ordinary["violations"], [])
            self.assertIn("dependencyMarker", {row["name"] for row in ordinary["declarations"]})

            # The corrected audit must see the local nonstandard axiom.
            report, = AUDIT.audit_groups(package, ["Tests.Main"])
            self.assertIn("localAuditSentinel", [row["declaration"] for row in report["violations"]])
            names = {row["name"] for row in report["declarations"]}
            self.assertIn("localMarker", names)
            self.assertNotIn("dependencyMarker", names)

            (package / ".lake/build/lib/lean/Tests/Main.olean").unlink()
            with self.assertRaisesRegex(FileNotFoundError, "missing local audit artifact"):
                AUDIT.audit_groups(package, ["Tests.Main"])


if __name__ == "__main__":
    unittest.main()
