"""The local replacement for expensive CI must never report partial work as green."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from periodic_check import ROOT, Step, run_steps, validation_steps


class PeriodicCheckTests(unittest.TestCase):
    def test_failure_stops_before_later_commands_and_keeps_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            steps = [Step("first", root, (sys.executable, "-c", "print('first completed')")),
                     Step("fails", root, (sys.executable, "-c", "raise SystemExit(7)")),
                     Step("never", root, (sys.executable, "-c", "raise AssertionError('must not run')"))]
            output = root / "evidence"
            self.assertEqual(run_steps(steps, output, "source-revision", True), 7)
            report = json.loads((output / "summary.json").read_text())
            self.assertEqual(report["status"], "failed")
            self.assertEqual(report["revision"], "source-revision")
            self.assertTrue(report["workingTreeDirty"])
            self.assertEqual([step["exitCode"] for step in report["steps"]], [0, 7])
            self.assertIn("first completed", Path(report["steps"][0]["log"]).read_text())
            self.assertFalse((output / "03-never.log").exists())

    def test_missing_tool_and_empty_plan_cannot_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "evidence"
            self.assertEqual(run_steps([Step("missing", root, (str(root / "missing-tool"),))], output, "rev"), 127)
            self.assertEqual(json.loads((output / "summary.json").read_text())["status"], "failed")
            with self.assertRaises(ValueError):
                run_steps([], root / "empty", "rev")

    def test_all_commands_must_pass_and_old_evidence_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "evidence"
            steps = [Step("works", root, (sys.executable, "-c", "print('done')"))]
            self.assertEqual(run_steps(steps, output, "rev"), 0)
            report = json.loads((output / "summary.json").read_text())
            self.assertEqual(report["status"], "passed")
            self.assertGreaterEqual(report["steps"][0]["seconds"], 0)
            with self.assertRaises(FileExistsError):
                run_steps(steps, output, "new-rev")

    def test_new_contracts_are_built_before_strict_audits_without_duplicate_wnear(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, manifest in [("linkdrop", "lakefile.toml"),
                                   ("next-contract", "lakefile.lean"),
                                   ("w-near", "lakefile.toml")]:
                project = root / "contracts" / name / "verification"
                project.mkdir(parents=True)
                (project / manifest).touch()
            # A dataset folder with no verification project must not be audited.
            (root / "contracts" / "not-started").mkdir()
            steps = validation_steps(root, root / "nearcore")
            names = [step.name for step in steps]
            builds = [step for step in steps if step.name.startswith("contract-")]
            self.assertEqual([step.name for step in builds],
                             ["contract-linkdrop-build", "contract-next-contract-build"])
            for step in builds:
                name = step.directory.parent.name
                audit_name = f"audit-contract-{name}"
                self.assertLess(names.index(step.name), names.index(audit_name))
                audit = steps[names.index(audit_name)]
                self.assertIn("--wfail", step.command)
                self.assertIn("--no-build", audit.command)
                self.assertNotIn("--allow-sorry", audit.command)
            self.assertEqual(names.count("audit-wnear"), 1)
            self.assertNotIn("audit-contract-w-near", names)

    def test_plan_needs_no_native_checkout_and_execution_requires_one(self):
        command = [sys.executable, str(ROOT / "tools/periodic_check.py")]
        plan = subprocess.run(command + ["--plan"], text=True, capture_output=True)
        self.assertEqual(plan.returncode, 0, plan.stderr)
        self.assertIn("chain-reference-build:", plan.stdout)
        self.assertIn("audit-wnear:", plan.stdout)
        self.assertIn("chain-action_randomness:", plan.stdout)
        refused = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(refused.returncode, 2)
        self.assertIn("--nearcore", refused.stderr)


if __name__ == "__main__":
    unittest.main()
