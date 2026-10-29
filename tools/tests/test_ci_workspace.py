"""Run the workflows' real cleanup commands against a warm workspace."""

from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[2]


class WorkspaceCleanupTests(unittest.TestCase):
    def test_previous_evidence_is_removed_and_build_caches_survive(self):
        for workflow in (ROOT / ".github/workflows").glob("*.yml"):
            scripts = re.findall(
                r"      - name: Clean sources and previous evidence; keep build caches\n"
                r"        run: \|\n((?:          .*\n)+)", workflow.read_text(),
            )
            self.assertTrue(scripts, f"{workflow.name}: missing workspace cleanup")
            for index, script in enumerate(scripts):
                with self.subTest(workflow=workflow.name, job=index), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    subprocess.run(["git", "init", "-q", directory], check=True)
                    (root / ".gitignore").write_text(".lake/\ntarget/\naudit/\n/reference-nearcore/\n")
                    (root / "Source.lean").write_text("tracked source\n")
                    subprocess.run(["git", "add", "."], cwd=root, check=True)
                    caches = ["near-lean/.lake/packages/cache", "near-lean/vm/.lake/build/cache",
                              "tools/runtime-conformance/target/cache", "reference-nearcore/.git/HEAD"]
                    evidence = ["audit/old.json", "audit/nested/report.json", "Scratch.lean"]
                    for name in caches + evidence:
                        path = root / name
                        path.parent.mkdir(parents=True, exist_ok=True)
                        path.write_text("previous run\n")
                    subprocess.run(["bash", "-e", "-c", textwrap.dedent(script)],
                                   cwd=root, check=True, capture_output=True)
                    for name in caches + ["Source.lean", ".gitignore"]:
                        self.assertTrue((root / name).is_file(), name)
                    for name in evidence:
                        self.assertFalse((root / name).exists(), name)


if __name__ == "__main__":
    unittest.main()
