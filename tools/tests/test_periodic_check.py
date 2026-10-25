"""The local replacement for expensive CI must never report partial work as green."""

from datetime import date, timedelta
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from periodic_check import (PINS_MAX_AGE_DAYS, ROOT, SECTIONS, Step, due_sections, read_ledger,
                            record_sections, run_steps, validation_steps)


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

    def test_new_contracts_are_built_before_strict_audits_without_duplicate_adapters(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, manifest in [("next-contract", "lakefile.lean"),
                                   ("other", "lakefile.toml"),
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
                             ["contract-next-contract-build", "contract-other-build"])
            for step in builds:
                name = step.directory.parent.name
                audit_name = f"audit-contract-{name}"
                self.assertLess(names.index(step.name), names.index(audit_name))
                audit = steps[names.index(audit_name)]
                self.assertIn("--wfail", step.command)
                self.assertIn("--no-build", audit.command)
                self.assertNotIn("--allow-sorry", audit.command)
            # Contracts with a model instance keep one audit, tolerating only the open refinement.
            for report, contract in [("wnear", "w-near")]:
                self.assertEqual(names.count(f"audit-{report}"), 1)
                self.assertNotIn(f"audit-contract-{contract}", names)
                audit = steps[names.index(f"audit-{report}")]
                self.assertIn("--allow-sorry-module", audit.command)
                self.assertLess(names.index(f"{report}-adapter-build"), names.index(f"audit-{report}"))

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


def git(root: Path, *args: str) -> str:
    # No detached auto-maintenance: it can still be writing to .git when tearDown removes it.
    return subprocess.check_output(["git", "-c", "user.name=t", "-c", "user.email=t@t",
                                    "-c", "maintenance.auto=false", "-c", "gc.auto=0", *args],
                                   cwd=root, text=True).strip()


def commit_file(root: Path, name: str) -> None:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(name + "\n")
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", name)


class LedgerTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        git(self.root, "init", "-q")
        commit_file(self.root, "README.md")
        self.ledger = self.root / "reports/periodic/LEDGER.json"
        self.ledger.parent.mkdir(parents=True)

    def tearDown(self):
        self.directory.cleanup()

    def record_all(self):
        record_sections(self.root, self.ledger, list(SECTIONS), "reports/periodic/today/README.md", ["SAF-1"])

    def test_unrecorded_sections_are_due_and_recorded_ones_are_not(self):
        self.assertEqual([name for name, _ in due_sections(self.root, {})], list(SECTIONS))
        self.record_all()
        ledger = read_ledger(self.ledger)
        self.assertEqual(ledger["divergence"]["issues"], ["SAF-1"])
        self.assertEqual(due_sections(self.root, ledger), [])

    def test_only_sections_watching_changed_paths_become_due(self):
        self.record_all()
        commit_file(self.root, "notes/design/X.md")
        self.assertEqual([name for name, _ in due_sections(self.root, read_ledger(self.ledger))],
                         ["docs", "features"])
        commit_file(self.root, "near-lean/runtime/A.lean")
        due = dict(due_sections(self.root, read_ledger(self.ledger)))
        self.assertIn("divergence", due)
        self.assertEqual(due["divergence"], f"1 files changed since {git(self.root, 'rev-parse', 'HEAD~2')[:7]}")

    def test_committing_the_check_output_does_not_make_it_due_again(self):
        self.record_all()
        commit_file(self.root, "reports/periodic/today/README.md")
        self.assertEqual(due_sections(self.root, read_ledger(self.ledger)), [])

    def test_pins_are_due_by_age_and_unknown_commits_are_due(self):
        self.record_all()
        ledger = read_ledger(self.ledger)
        later = date.fromisoformat(ledger["pins"]["date"]) + timedelta(days=PINS_MAX_AGE_DAYS)
        self.assertEqual([name for name, _ in due_sections(self.root, ledger, later)], ["pins"])
        ledger["build"]["commit"] = "0" * 40
        self.assertIn("not in this repository", dict(due_sections(self.root, ledger))["build"])

    def test_unknown_sections_are_refused(self):
        with self.assertRaises(ValueError):
            record_sections(self.root, self.ledger, ["bulid"], "report", [])
        self.assertFalse(self.ledger.exists())


if __name__ == "__main__":
    unittest.main()
