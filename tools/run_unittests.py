#!/usr/bin/env python3
"""Run a `unittest discover` suite with its tests spread over worker processes.

The same tests as `python3 -m unittest discover -s DIR -p PATTERN`, with each
discovered module suite running in a worker. Keeping suites intact preserves
module/class fixtures and discovery hooks. Prints failures and a summary;
exits nonzero if any test failed or errored.
"""

import argparse
from concurrent.futures import ProcessPoolExecutor
import io
import os
from pathlib import Path
import sys
import time
import unittest


def flatten(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from flatten(item)
        else:
            yield item


def prepare(start):
    sys.path.insert(0, start)


def run_suite(suite):
    name = next(flatten(suite)).id().rsplit(".", 2)[0]
    stream = io.StringIO()
    started = time.monotonic()
    result = unittest.TextTestRunner(stream=stream, verbosity=0).run(suite)
    return (name, result.testsRun,
            len(result.failures) + len(result.errors) + len(result.unexpectedSuccesses),
            len(result.skipped), time.monotonic() - started, stream.getvalue())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-s", "--start", required=True, help="directory to discover tests in")
    parser.add_argument("-p", "--pattern", default="test*.py")
    parser.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    args = parser.parse_args()
    if args.jobs is not None and args.jobs < 1:
        parser.error("workers must be positive")
    start = str(Path(args.start).resolve())
    prepare(start)
    suites = [suite for suite in unittest.TestLoader().discover(start, args.pattern)
              if suite.countTestCases()]
    if not suites:
        print(f"no tests found in {args.start}")
        return 1
    began = time.monotonic()
    ran = failed = skipped = 0
    slowest = []
    jobs = min(args.jobs or 1, len(suites))
    with ProcessPoolExecutor(jobs, initializer=prepare, initargs=(start,)) as pool:
        for test_id, count, failures, skips, seconds, output in pool.map(run_suite, suites):
            ran, failed, skipped = ran + count, failed + failures, skipped + skips
            slowest.append((seconds, test_id))
            if failures:
                print(f"FAIL {test_id}\n{output}", flush=True)
    for seconds, test_id in sorted(slowest, reverse=True)[:5]:
        print(f"{seconds:6.1f}s {test_id}")
    status = f"{failed} failed" if failed else "OK"
    print(f"Ran {ran} tests in {time.monotonic() - began:.1f}s with {jobs} workers: "
          f"{status}" + (f" ({skipped} skipped)" if skipped else ""))
    return int(bool(failed))


if __name__ == "__main__":
    raise SystemExit(main())
