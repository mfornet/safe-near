"""Offline tests of the axiom audit's policy: CLI options and which violations fail.

The real-Lean artifact regression is check_axiom_audit.py.
"""

import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("axiom_audit", ROOT / "tools/axiom-audit.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class AxiomAuditPolicyTests(unittest.TestCase):
    def test_cli_rejects_missing_or_ambiguous_open_module_policy(self):
        with tempfile.TemporaryDirectory(prefix="safe-near-audit-policy-") as directory:
            report = Path(directory) / "report.json"
            base = ["python3", str(ROOT / "tools/axiom-audit.py"),
                    str(ROOT / "near-lean/wasm"), "--report", str(report), "--no-build"]
            for options, message in [
                (["--allow-sorry-module", "Wasm.DoesNotExist"], "allowed sorry module is absent"),
                (["--allow-sorry", "--allow-sorry-module", "Wasm.Exec"], "cannot be combined"),
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


class StatementPinTests(unittest.TestCase):
    def statement(self, name, text, hash=1, module="Spec"):
        return dict(module=module, name=name, text=text, hash=hash)

    def test_pin_file_lists_each_statement_once_and_rejects_missing_pins(self):
        with tempfile.TemporaryDirectory(prefix="safe-near-pins-") as directory:
            config = Path(directory) / "statements.json"
            config.write_text('{"modules": ["Spec"], "declarations": ["P.closes"]}')
            spec = self.statement("Spec.Holds", "def Spec.Holds : Prop :=\n  True", 255)
            proof = self.statement("P.closes", "theorem P.closes : Spec.Holds", 2, "Proofs")
            # Split audit groups both see imported statements; the file has them once.
            rendered = AUDIT.render_statements(config, [dict(statements=[spec, proof]),
                                                        dict(statements=[spec])])
            self.assertEqual(rendered.count("`Spec.Holds`"), 1)
            self.assertIn("(hash `00000000000000ff`)", rendered)
            self.assertLess(rendered.index("## Proofs"), rendered.index("## Spec"))
            with self.assertRaisesRegex(RuntimeError, "P.closes"):
                AUDIT.render_statements(config, [dict(statements=[spec])])

    def test_changed_statement_fails_until_the_pin_file_is_updated(self):
        with tempfile.TemporaryDirectory(prefix="safe-near-pins-") as directory:
            config = Path(directory) / "statements.json"
            config.write_text('{"modules": ["Spec"]}')
            original = [dict(statements=[self.statement("Spec.Holds", "def Spec.Holds : Prop :=\n  True")])]
            weakened = [dict(statements=[self.statement("Spec.Holds", "def Spec.Holds : Prop :=\n  False", 2)])]
            with contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertFalse(AUDIT.check_statements(config, original, update=False))
                self.assertTrue(AUDIT.check_statements(config, original, update=True))
                self.assertTrue(AUDIT.check_statements(config, original, update=False))
                self.assertFalse(AUDIT.check_statements(config, weakened, update=False))
            self.assertIn("-  True\n+  False", output.getvalue())
            self.assertIn("True", (Path(directory) / "STATEMENTS.md").read_text())


if __name__ == "__main__":
    unittest.main()
