"""The pure analysis of `tools/localnet/follow_accept.py`: head lookup, lag series and the report numbers."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "localnet"))

import follow_accept  # noqa: E402


def rows(*applied, start=1000.0, blocks=1):
    return [{"unixMs": int((start + i) * 1000), "applied": a, "blocks": blocks} for i, a in enumerate(applied)]


class HeadAt(unittest.TestCase):
    def test_last_sample_not_after(self):
        samples = [(1.0, 10), (2.0, 11), (3.0, 12)]
        self.assertIsNone(follow_accept.head_at(samples, 0.5))
        self.assertEqual(follow_accept.head_at(samples, 2.0), 11)
        self.assertEqual(follow_accept.head_at(samples, 2.9), 11)
        self.assertEqual(follow_accept.head_at(samples, 9.0), 12)


class LagSeries(unittest.TestCase):
    def test_lag_is_head_minus_applied(self):
        samples = [(1000.0, 100), (1001.0, 101), (1002.0, 102)]
        series = follow_accept.lag_series(rows(95, 100, 105), samples)
        self.assertEqual([lag for _, _, lag in series], [5, 1, 0])  # never negative

    def test_before_first_block_is_skipped(self):
        samples = [(1000.0, 100)]
        self.assertEqual(follow_accept.lag_series(rows(0, 0, blocks=0), samples), [])

    def test_before_first_head_sample_is_skipped(self):
        self.assertEqual(follow_accept.lag_series(rows(5), [(2000.0, 9)]), [])


class Analyse(unittest.TestCase):
    series = [(10.0, 100, 50), (11.0, 100, 20), (12.0, 101, 3), (13.0, 102, 12), (14.0, 103, 2), (15.0, 104, 1)]

    def test_never_reached(self):
        out = follow_accept.analyse([(1.0, 10, 30)], 0.0, 10, None)
        self.assertEqual(out["reachedAfterSeconds"], None)

    def test_numbers_after_reaching(self):
        out = follow_accept.analyse(self.series, 8.0, 10, None)
        self.assertEqual(out["reachedAfterSeconds"], 4.0)
        self.assertEqual(out["maxLagAfterReach"], 12)
        self.assertEqual(out["secondsAboveLimit"], 1)
        self.assertEqual(out["followedSeconds"], 3.0)
        self.assertEqual(out["medianLag"], 2.5)

    def test_burst(self):
        out = follow_accept.analyse(self.series, 8.0, 10, 12.5)
        self.assertEqual(out["burstPeakLag"], 12)
        self.assertEqual(out["burstPeakAfterSeconds"], 0.5)
        self.assertEqual(out["burstCaughtUpAfterSeconds"], 1.5)


if __name__ == "__main__":
    unittest.main()
