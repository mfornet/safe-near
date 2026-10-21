"""Offline custody and historical/synthetic separation checks (not execution evidence)."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1] / 'history-replay'
SPEC = importlib.util.spec_from_file_location('historical_bundle', HERE / 'history.py')
history = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(history)
PREP = importlib.util.spec_from_file_location('historical_build', HERE / 'prepare.py')
prepare = importlib.util.module_from_spec(PREP)
PREP.loader.exec_module(prepare)


def capture():
    expected = dict(stateRoot='state', outcomeRoot='outcome', outcomes='00', outgoingReceipts='00',
                    gasBurnt='1', balanceBurnt='2')
    request = dict(format='safe-near-runtime-witness-v1', sourceRevision=history.REVISION,
                   context=dict(blockHeight=100, shardId=3, isNewChunk=True),
                   preStateRoot='00', flatStorageCosts=True, validatorAccountsUpdate=None,
                   transactions='00', transactionValidity=[], incomingReceipts='00',
                   epochQueries=dict(chain_id='mainnet'), witness='00', nativeExpected=expected,
                   captureTelemetry=dict(originalStats='00', bandwidthSchedulerTimeToRunMs='1'))
    archive = dict(format='safe-near-archive-anchor-v1', archiveComparisonEstablished=True,
                   chainId='mainnet', blockHeight=100, shardId=3, blockHash='block', **expected)
    return request, archive


class HistoricalBundleTests(unittest.TestCase):
    def test_checked_in_public_fixture_custody_and_archive_binding(self):
        directory = HERE / 'fixtures/mainnet-220938800-shard11'
        manifest = history.read(directory / 'manifest.json')
        self.assertEqual(set(manifest['files']), set(history.FILES))
        for name, digest in manifest['files'].items():
            self.assertEqual(history.sha(directory / name), digest)
        request = history.read(directory / 'request.json')
        archive = history.read(directory / 'archive.json')
        history.validate_capture(request, archive)
        self.assertEqual(manifest['comparisonScope'], history.COMPARISON_SCOPE)
        self.assertEqual(manifest['blockHash'], archive['blockHash'])
        self.assertFalse(manifest['leanExecutionEstablished'])

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.request, self.archive = capture()
        self.binary = self.root / 'replay'
        self.binary.write_bytes(b'fixture executable')
        self.paths = [self.root / ('source-' + name) for name in history.FILES]
        for path, value in zip(self.paths, (self.request, self.archive,
                dict(sourceRevision=history.REVISION, checkOnly=False))):
            history.write(path, value)
        self.destination = self.root / 'bundle'
        self.evidence = dict(archiveVerified=True, offlineReplayVerified=True)

    def package(self):
        with patch.object(history, 'replay', return_value=self.evidence):
            return history.package(*self.paths, self.destination, self.binary)

    def test_portable_assets_and_candidate_does_not_receive_expected_output(self):
        self.package()
        moved = self.root / 'relocated'
        self.destination.rename(moved)
        model = self.root / 'candidate'
        model.write_bytes(b'candidate')
        with patch.object(history, 'replay', return_value=self.evidence.copy()), \
                patch.object(history, 'execute', return_value=self.request['nativeExpected']) as run:
            result = history.verify(moved, self.binary, model)
        self.assertTrue(result['leanExecutionEstablished'])
        self.assertNotIn('nativeExpected', run.call_args.args[1])
        self.assertNotIn('captureTelemetry', run.call_args.args[1])
        self.assertFalse(history.read(moved / 'manifest.json')['leanExecutionEstablished'])

    def test_mutated_asset_is_rejected_before_execution(self):
        self.package()
        (self.destination / 'request.json').write_text('{}')
        with patch.object(history, 'replay') as run:
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                history.verify(self.destination, self.binary)
            run.assert_not_called()

    def test_comparison_scope_cannot_silently_exclude_another_output(self):
        self.package()
        path = self.destination / 'manifest.json'
        manifest = history.read(path)
        manifest['comparisonScope']['excludedTelemetry'].append('outcomes')
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'comparison scope'):
            history.verify(self.destination, self.binary)

    def test_incomplete_manifest_and_path_injection_are_rejected(self):
        self.package()
        manifest_path = self.destination / 'manifest.json'
        manifest = history.read(manifest_path)
        manifest['files']['../outside.json'] = 'bad'
        manifest_path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'incomplete or unknown'):
            history.verify(self.destination, self.binary)
        manifest_path.unlink()
        with self.assertRaisesRegex(ValueError, 'ordinary file'):
            history.verify(self.destination, self.binary)

    def test_failed_replay_does_not_publish_a_bundle(self):
        with patch.object(history, 'replay', side_effect=ValueError('missing witness')):
            with self.assertRaisesRegex(ValueError, 'missing witness'):
                history.package(*self.paths, self.destination, self.binary)
        self.assertFalse(self.destination.exists())

    def test_existing_destination_is_never_overwritten(self):
        self.package()
        before = history.sha(self.destination / 'manifest.json')
        with self.assertRaises(FileExistsError):
            self.package()
        self.assertEqual(history.sha(self.destination / 'manifest.json'), before)

    def test_archive_runtime_mismatches_and_synthetic_network_fail(self):
        for key in ('blockHeight', 'shardId', 'stateRoot', 'outcomeRoot', 'outcomes',
                    'outgoingReceipts', 'gasBurnt', 'balanceBurnt'):
            archive = copy.deepcopy(self.archive)
            archive[key] = 'changed'
            with self.subTest(key=key), self.assertRaises(ValueError):
                history.validate_capture(self.request, archive)
        self.request['epochQueries']['chain_id'] = self.archive['chainId'] = 'synthetic'
        with self.assertRaisesRegex(ValueError, 'mainnet or testnet'):
            history.validate_capture(self.request, self.archive)

    def test_anchor_marker_alone_cannot_replace_native_verification(self):
        with patch.object(history, 'execute', side_effect=[dict(sourceRevision=history.REVISION),
                dict(archiveVerified=True, observations={})]):
            with self.assertRaisesRegex(ValueError, 'complete offline'):
                history.replay(self.request, self.archive, self.binary)

    def test_unknown_fields_duplicate_json_and_symlinks_fail(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            history.loads('{"a":1,"a":2}')
        value = copy.deepcopy(self.request)
        value['ignored'] = 1
        with self.assertRaisesRegex(ValueError, 'unknown runtime'):
            history.validate_capture(value, self.archive)
        link = self.root / 'symlink'
        link.symlink_to(self.paths[0])
        with self.assertRaisesRegex(ValueError, 'ordinary file'):
            history.read(link)

    def test_guarded_overlay_rejects_a_different_upstream_seam(self):
        self.assertEqual(prepare.replace_once('one old two', 'old', 'new'), 'one new two')
        for value in ('nothing matching', 'old old'):
            with self.assertRaisesRegex(ValueError, 'seam changed'):
                prepare.replace_once(value, 'old', 'new')


if __name__ == '__main__':
    unittest.main()
