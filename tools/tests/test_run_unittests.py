"""Exercise the process runner through its CLI, including spawned workers."""

from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest


RUNNER = Path(__file__).resolve().parents[1] / "run_unittests.py"


class ParallelRunnerTests(unittest.TestCase):
    def run_fixture(self, source, *args):
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / "test_fixture.py").write_text(textwrap.dedent(source))
            return subprocess.run(
                [sys.executable, str(RUNNER), "-s", directory, "-j", "2", *args],
                text=True, capture_output=True, timeout=30,
            )

    def test_discovery_hooks_and_shared_fixtures_are_preserved(self):
        result = self.run_fixture('''
            import unittest
            module_setups = class_setups = 0
            def setUpModule():
                global module_setups
                module_setups += 1
            def tearDownModule():
                assert module_setups == class_setups == 1
            class Shared(unittest.TestCase):
                @classmethod
                def setUpClass(cls):
                    global class_setups
                    class_setups += 1
                    cls.values = []
                @classmethod
                def tearDownClass(cls):
                    assert cls.values == [1, 2]
                def test_first(self):
                    self.values.append(1)
                def test_second(self):
                    self.assertEqual(self.values, [1])
                    self.values.append(2)
                def test_excluded(self):
                    self.fail("load_tests must exclude this test")
            def load_tests(loader, tests, pattern):
                return unittest.TestSuite([Shared("test_first"), Shared("test_second")])
        ''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Ran 2 tests", result.stdout)

    def test_unexpected_success_fails(self):
        result = self.run_fixture('''
            import unittest
            class Unexpected(unittest.TestCase):
                @unittest.expectedFailure
                def test_passes(self):
                    pass
        ''')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("UNEXPECTED SUCCESS", result.stdout)

    def test_import_failure_retains_original_error(self):
        result = self.run_fixture('raise RuntimeError("discovery failure evidence")')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("discovery failure evidence", result.stdout + result.stderr)

    def test_class_fixture_error_fails_even_without_running_tests(self):
        result = self.run_fixture('''
            import unittest
            class Broken(unittest.TestCase):
                @classmethod
                def setUpClass(cls):
                    raise RuntimeError("fixture failure evidence")
                def test_never_runs(self):
                    pass
        ''')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("fixture failure evidence", result.stdout)

    def test_expected_failures_and_skips_pass(self):
        result = self.run_fixture('''
            import unittest
            class Outcomes(unittest.TestCase):
                @unittest.expectedFailure
                def test_expected(self):
                    self.fail("expected")
                @unittest.skip("optional dependency")
                def test_skip(self):
                    pass
        ''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Ran 2 tests", result.stdout)
        self.assertIn("1 skipped", result.stdout)

    def test_empty_discovery_and_invalid_workers_fail(self):
        for args in [(), ("-j", "0")]:
            with self.subTest(args=args):
                result = self.run_fixture("", *args)
                self.assertNotEqual(result.returncode, 0)

    def test_module_fixture_skip_is_successful(self):
        result = self.run_fixture('''
            import unittest
            def setUpModule():
                raise unittest.SkipTest("optional module dependency")
            class Optional(unittest.TestCase):
                def test_never_runs(self):
                    self.fail("module must be skipped")
        ''')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("1 skipped", result.stdout)


if __name__ == "__main__":
    unittest.main()
