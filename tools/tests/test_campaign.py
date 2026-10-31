"""The campaign driver on fake backends: profiles and fallbacks, exhaustion,
the file guard, repair rounds, acceptance, and the results record."""

from datetime import datetime, timedelta, timezone
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from campaign import backends, driver  # noqa: E402
from campaign.config import DEFAULT_PROFILES, Config, ConfigError, ExhaustionState  # noqa: E402

FAKE_CONFIG = {
    "backends": {"a": {"kind": "fake"}, "b": {"kind": "fake"}, "c": {"kind": "fake-agent"}},
    "profiles": {
        "default": {"fallbacks": ["spare"], "roles": {
            "architect": [{"backend": "a", "attempts": 1}], "auditor": [{"backend": "a", "attempts": 1}],
            "prover": [{"backend": "a", "model": "m1", "attempts": 2}, {"backend": "b", "model": "m2", "attempts": 1}],
            "grinder": [{"backend": "a"}], "runner": [{"backend": "c", "attempts": 1}],
            "integrator": [{"backend": "a"}]}},
        "spare": {"fallbacks": [], "roles": {
            "architect": [{"backend": "b"}], "auditor": [{"backend": "b"}],
            "prover": [{"backend": "c", "model": "m3", "attempts": 1}], "grinder": [{"backend": "b"}],
            "runner": [{"backend": "b"}], "integrator": [{"backend": "b"}]}},
    },
}


class ProfileTests(unittest.TestCase):
    def test_shipped_profiles_validate(self):
        config = Config.load(DEFAULT_PROFILES)
        self.assertIn("default", config.profiles)
        for role in ("architect", "prover", "grinder"):
            self.assertTrue(config.chain(role))

    def test_exhausted_backend_is_replaced_by_fallback_profiles(self):
        config = Config.load(DEFAULT_PROFILES)
        chain = config.chain("prover", "default", exhausted={"claude"})
        self.assertTrue(chain)
        self.assertTrue(all(t.backend != "claude" for t in chain))
        self.assertEqual(chain[0].backend, "codex")
        only_api = config.chain("architect", "default", exhausted={"claude", "codex"})
        self.assertEqual([t.backend for t in only_api], ["deepseek"])
        self.assertEqual(config.chain("architect", "default", exhausted={"claude", "codex", "deepseek"}), [])

    def test_chain_order_and_dedupe(self):
        config = Config(FAKE_CONFIG)
        labels = [t.label for t in config.chain("prover")]
        self.assertEqual(labels, ["a:m1", "b:m2", "c:m3"])
        with self.assertRaises(ConfigError):
            config.chain("prover", "missing")

    def test_invalid_profiles_are_rejected(self):
        broken = json.loads(json.dumps(FAKE_CONFIG))
        broken["profiles"]["default"]["roles"]["prover"] = [{"backend": "nope"}]
        with self.assertRaisesRegex(ConfigError, "unknown backend"):
            Config(broken)
        broken = json.loads(json.dumps(FAKE_CONFIG))
        del broken["profiles"]["default"]["roles"]["runner"]
        with self.assertRaisesRegex(ConfigError, "no tier"):
            Config(broken)


class ExhaustionTests(unittest.TestCase):
    def test_marks_expire(self):
        with tempfile.TemporaryDirectory() as directory:
            state = ExhaustionState(Path(directory) / "x.json", reset_hours=2)
            now = datetime(2026, 10, 31, 12, 0, tzinfo=timezone.utc)
            state.mark("claude", now)
            self.assertEqual(state.active(now), {"claude"})
            self.assertEqual(state.active(now + timedelta(hours=3)), set())
            state.clear("claude")
            self.assertEqual(state.active(now), set())


class FileBlockTests(unittest.TestCase):
    def test_blocks_are_written_inside_the_worktree_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            text = "note\n<<<FILE a/b.lean>>>\ntheorem t : True := trivial\n<<<END>>>\n"
            self.assertEqual(backends.apply_file_blocks(text, root), ["a/b.lean"])
            self.assertEqual((root / "a/b.lean").read_text(), "theorem t : True := trivial\n")
            with self.assertRaisesRegex(ValueError, "leaves"):
                backends.apply_file_blocks("<<<FILE ../x>>>\nhi\n<<<END>>>", root)


class DriverTests(unittest.TestCase):
    """A task whose check is `grep` on one file, run on fake backends in a temporary repository."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", "-b", "main", str(self.root)], check=True)
        (self.root / "pkg").mkdir()
        (self.root / "pkg/Target.lean").write_text("sorry\n")
        (self.root / "pkg/Other.lean").write_text("keep\n")
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "init")
        (self.root / "campaign/tasks").mkdir(parents=True)
        self.task = {"id": "t1", "role": "prover", "kind": "lean-proof", "title": "close Target",
                     "brief_text": "Replace sorry by a proof.", "package": "pkg", "files": ["Target.lean"],
                     "check": ["grep -q done Target.lean"], "base": "main", "rounds": 2, "timeout_minutes": 1}
        (self.root / "campaign/tasks/t1.json").write_text(json.dumps(self.task))
        self.config = Config(FAKE_CONFIG)
        self.pool = {name: backends.make(name, spec) for name, spec in self.config.backends.items()}
        backends.Fake.responses = {}
        self.logs = []

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, text=True, check=True)

    def run_task(self, profile="default"):
        return driver.run_task(self.root, self.task, self.config, profile, self.pool, log=self.logs.append)

    def results(self):
        return [json.loads(l) for l in (self.root / "campaign/results.jsonl").read_text().splitlines()]

    def test_repair_round_then_acceptance_and_commit(self):
        backends.Fake.responses["a"] = ["<<<FILE Target.lean>>>\nnot yet\n<<<END>>>",
                                        "<<<FILE Target.lean>>>\ndone\n<<<END>>>"]
        accepted = self.run_task()
        self.assertIsNotNone(accepted)
        self.assertEqual(accepted["attempt"], 1)
        self.assertEqual(accepted["model"], "m1")
        shown = self.git("show", "--stat", "--format=%s", accepted["commit"]).stdout
        self.assertIn("t1: close Target", shown)
        self.assertIn("Target.lean", shown)
        self.assertEqual(self.git("show", f"{accepted['branch']}:pkg/Target.lean").stdout, "done\n")
        self.assertFalse((self.root / ".campaign/worktrees/t1").exists())
        self.assertEqual([r["accepted"] for r in self.results()], [True])

    def test_changes_outside_the_task_are_rejected_then_escalated(self):
        backends.Fake.responses["a"] = ["<<<FILE Other.lean>>>\ndone\n<<<END>>>\n<<<FILE Target.lean>>>\ndone\n<<<END>>>",
                                        "<<<FILE Target.lean>>>\nstill wrong\n<<<END>>>",
                                        "<<<FILE Target.lean>>>\nstill wrong\n<<<END>>>"]
        backends.Fake.responses["b"] = ["<<<FILE Target.lean>>>\ndone\n<<<END>>>"]
        accepted = self.run_task()
        self.assertEqual((accepted["backend"], accepted["model"]), ("b", "m2"))
        rows = self.results()
        self.assertEqual([r["accepted"] for r in rows], [False, False, True])
        self.assertIn("outside the task: pkg/Other.lean", rows[0]["detail"])
        self.assertEqual(self.git("show", "campaign/t1:pkg/Other.lean").stdout, "keep\n")

    def test_exhaustion_switches_backend_and_is_recorded(self):
        backends.Fake.responses["a"] = ["<<<EXHAUSTED>>>"]
        backends.Fake.responses["b"] = ["<<<FILE Target.lean>>>\ndone\n<<<END>>>"]
        accepted = self.run_task()
        self.assertEqual(accepted["backend"], "b")
        rows = self.results()
        self.assertTrue(rows[0]["exhausted"])
        self.assertEqual(ExhaustionState(self.root / "campaign/.state/exhausted.json").active(), {"a"})
        # A later task skips the exhausted backend without trying it.
        backends.Fake.responses["b"] = ["<<<FILE Target.lean>>>\ndone\n<<<END>>>"]
        again = self.run_task()
        self.assertEqual(again["backend"], "b")
        self.assertEqual(backends.Fake.responses["a"], [])

    def test_agentic_backend_edits_itself_and_every_tier_can_fail(self):
        backends.Fake.responses["c"] = ["<<<FILE pkg/Target.lean>>>\ndone\n<<<END>>>"]
        task = dict(self.task, role="runner")
        accepted = driver.run_task(self.root, task, self.config, "default", self.pool, log=self.logs.append)
        self.assertEqual(accepted["backend"], "c")
        backends.Fake.responses = {"a": ["nothing"] * 2, "b": ["nothing"], "c": ["nothing"]}
        self.assertIsNone(self.run_task())
        self.assertIn("t1: no tier left", self.logs)

    def test_summary_and_cli(self):
        backends.Fake.responses["a"] = ["<<<FILE Target.lean>>>\ndone\n<<<END>>>"]
        config = self.root / "profiles.json"
        config.write_text(json.dumps(FAKE_CONFIG))
        argv = ["--root", str(self.root), "--config", str(config)]
        self.assertEqual(driver.main(argv + ["run", "--parallel", "1"]), 0)
        self.assertEqual(driver.main(argv + ["run"]), 0)  # nothing left to run
        table = driver.summarize(self.root)
        self.assertEqual([(k, m, n, ok) for k, m, n, ok, _, _ in table], [("lean-proof", "a:m1", 1, 1)])
        self.assertEqual(driver.main(argv + ["status"]), 0)
        self.assertEqual(driver.main(argv + ["results"]), 0)
        self.assertEqual(driver.main(argv + ["new", "t2", "--role", "runner", "--kind", "report", "--title", "x"]), 0)
        self.assertTrue((self.root / "campaign/tasks/t2.json").exists())
        self.assertTrue((self.root / "campaign/briefs/t2.md").exists())

    def test_merge_recheck(self):
        backends.Fake.responses["a"] = ["<<<FILE Target.lean>>>\ndone\n<<<END>>>"]
        self.run_task()
        config = self.root / "profiles.json"
        config.write_text(json.dumps(FAKE_CONFIG))
        self.assertEqual(driver.main(["--root", str(self.root), "--config", str(config), "merge", "--into", "main"]), 0)
        worktrees = list((self.root / ".campaign/worktrees").glob("merge-*"))
        self.assertEqual(len(worktrees), 1)
        self.assertEqual((worktrees[0] / "pkg/Target.lean").read_text(), "done\n")


if __name__ == "__main__":
    unittest.main()
