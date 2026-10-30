"""Regression tests for serialization and conservative frontier reuse."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import wnear_blueprint as blueprint
import wnear_pipeline as pipeline


class PipelineTests(unittest.TestCase):
    def test_competing_pipeline_waits_for_lock(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            lock = root / 'pipeline.lock'
            script = ('import sys; from pathlib import Path; '
                      'sys.path.insert(0, sys.argv[1]); import wnear_pipeline as p; '
                      'p.WORK=Path(sys.argv[2]); p.LOCK=p.WORK/"pipeline.lock"; '
                      'exec("with p.pipeline_lock():\\n print(\\"acquired\\", flush=True)")')
            with patch.object(pipeline, 'WORK', root), patch.object(pipeline, 'LOCK', lock):
                with pipeline.pipeline_lock():
                    env = os.environ.copy()
                    env.pop(pipeline.FD_ENV, None)
                    child = subprocess.Popen([sys.executable, '-c', script, str(TOOLS), str(root)],
                                             stdout=subprocess.PIPE, text=True, env=env)
                    time.sleep(0.3)
                    self.assertIsNone(child.poll())
                out, _ = child.communicate(timeout=5)
                self.assertEqual(child.returncode, 0)
                self.assertEqual(out.strip(), 'acquired')

    def test_export_cache_is_keyed_and_strict_check_does_not_reuse(self):
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            manifest = {'nodes': [{'declaration': 'Example.t', 'method': 'test'}]}
            cache = work / 'frontier-export-cache.json'
            cache.write_text(json.dumps({'key': 'first', 'rows': [{'declaration': 'Example.t'}]}))
            with patch.object(blueprint, 'WORK', work), patch.object(blueprint, 'run') as run:
                rows = blueprint.export_lean(manifest, cache_key='first', reuse=True)
                self.assertEqual(rows[0]['declaration'], 'Example.t')
                run.assert_not_called()
                with self.assertRaises(FileNotFoundError):
                    blueprint.export_lean(manifest, cache_key='first', reuse=False)
                self.assertEqual(run.call_count, 1)

    def test_fingerprint_changes_when_import_artifact_changes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            lean = root / 'lean'
            lean.write_text('lean')
            imports = root / 'imports'
            imports.mkdir()
            artifact = imports / 'Dependency.olean'
            artifact.write_bytes(b'a')
            with patch.object(blueprint.subprocess, 'check_output', side_effect=[str(imports), str(lean)] * 2), \
                    patch.object(blueprint, 'record_phase'):
                before = blueprint.artifact_fingerprint('source')
                artifact.write_bytes(b'changed')
                after = blueprint.artifact_fingerprint('source')
            self.assertNotEqual(before, after)


if __name__ == '__main__':
    unittest.main()
