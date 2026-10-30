"""Local benchmark records preserve comparisons without publishing machine identity."""

from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verification_buildtime as buildtime


class VerificationBuildtimeTests(unittest.TestCase):
    def run_command(self, baseline, *args, seconds=28.0):
        result = {"seconds": seconds, "samples": [seconds], "jobs": 748,
                  "targets": ["Model", "Spec"]}
        with patch.object(sys, "argv", ["verification_buildtime", "--baseline", str(baseline), *args]), \
                patch.object(buildtime, "measure", return_value=result) as measure, \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            code = buildtime.main()
        return code, measure

    def test_record_and_compare_without_machine_identifiers(self):
        with tempfile.TemporaryDirectory() as directory:
            baseline = Path(directory) / "baseline.json"
            code, _ = self.run_command(baseline, "--record", "--targets", "Model", "Spec")
            self.assertEqual(code, 0)
            recorded = json.loads(baseline.read_text())
            self.assertEqual(set(recorded), {"w-near"})
            self.assertEqual(set(recorded["w-near"]),
                             {"seconds", "samples", "jobs", "targets", "recorded"})
            self.assertEqual(self.run_command(baseline, seconds=29.0)[0], 0)
            self.assertEqual(self.run_command(baseline, seconds=31.0)[0], 1)

    def test_missing_baseline_and_changed_targets_fail_before_building(self):
        with tempfile.TemporaryDirectory() as directory:
            baseline = Path(directory) / "baseline.json"
            code, measure = self.run_command(baseline)
            self.assertEqual(code, 2)
            measure.assert_not_called()
            self.run_command(baseline, "--record", "--targets", "Model", "Spec")
            code, measure = self.run_command(baseline, "--targets", "Other")
            self.assertEqual(code, 2)
            measure.assert_not_called()


if __name__ == "__main__":
    unittest.main()
