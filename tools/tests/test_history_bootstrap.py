"""Acquisition failure boundaries; these tests are not public replay evidence."""
import argparse
import fcntl
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1] / 'history-replay'
with patch.object(sys, 'path', [str(HERE)] + sys.path):
    spec = importlib.util.spec_from_file_location('history_bootstrap', HERE / 'bootstrap.py')
    bootstrap = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bootstrap)


class BootstrapBoundaries(unittest.TestCase):
    def test_fresh_node_false_sync_is_not_success(self):
        status = {'sync_info': {'syncing': False, 'latest_block_height': 9820210}}
        self.assertFalse(bootstrap.initialized_and_synced(status, 9820210))
        status['sync_info']['latest_block_height'] += 1
        self.assertTrue(bootstrap.initialized_and_synced(status, 9820210))
        status['sync_info']['syncing'] = True
        self.assertFalse(bootstrap.initialized_and_synced(status, 9820210))

    def test_concurrent_resume_is_rejected_before_configuration_or_network(self):
        with tempfile.TemporaryDirectory() as directory:
            home = Path(directory) / 'node'
            args = argparse.Namespace(near_home=home)
            with home.with_name('node.bootstrap.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                with patch.object(bootstrap, 'run_locked') as run:
                    with self.assertRaises(BlockingIOError):
                        bootstrap.run(args)
                    run.assert_not_called()

    def test_wrong_network_rpc_is_rejected_before_node_initialization(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / 'neard'
            binary.write_bytes(b'fake test executable')
            build = root / 'build.json'
            bootstrap.write(build, dict(sourceRevision=bootstrap.REVISION, checkOnly=False,
                neardBinarySha256=bootstrap.sha(binary),
                overlaySha256={bootstrap.NETWORK_OVERLAY: 'test'}))
            args = argparse.Namespace(near_home=root / 'node', neard=binary, build=build,
                direct_state_sync=True, max_seconds=1, max_gib=1, rpc='https://unused.test')
            with patch.object(bootstrap, 'rpc', return_value={'chain_id': 'testnet',
                    'protocol_version': 86}), patch.object(bootstrap, 'initialize') as init:
                with self.assertRaisesRegex(ValueError, 'must serve mainnet'):
                    bootstrap.run(args)
                init.assert_not_called()
            self.assertFalse(args.near_home.exists())
