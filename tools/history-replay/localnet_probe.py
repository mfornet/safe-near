#!/usr/bin/env python3
"""Test the archive exporter on an isolated local node, never as historical evidence."""
import argparse
import copy
import json
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import urllib.request

from history import HERE, read, execute, validate_capture


def free_port():
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        return sock.getsockname()[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, default=HERE / 'target/build.json')
    args = parser.parse_args()
    build = read(args.build)
    neard, replay = Path(build['neard']), Path(build['replay'])
    with tempfile.TemporaryDirectory(prefix='safe-near-archive-export-test-') as tmp:
        home = Path(tmp)
        log = (home / 'node.log').open('w')
        subprocess.run([str(neard), '--home', str(home), 'init', '--chain-id', 'history-export-localnet',
                        '--account-id', 'validator', '--test-seed', 'public-localnet-test', '--fast'],
                       stdout=log, stderr=log, check=True)
        config = read(home / 'config.json')
        rpc_port = free_port()
        config['rpc']['addr'] = f'127.0.0.1:{rpc_port}'
        config['network']['addr'] = f'127.0.0.1:{free_port()}'
        config['network']['boot_nodes'] = ''
        config['archive'] = False  # Recent retained state is sufficient for this local test.
        (home / 'config.json').write_text(json.dumps(config))
        genesis = read(home / 'genesis.json')
        height = genesis['genesis_height'] + 4
        node = subprocess.Popen([str(neard), '--home', str(home), 'run'], stdout=log, stderr=log)
        try:
            deadline = time.monotonic() + 50
            while time.monotonic() < deadline:
                if node.poll() is not None:
                    raise RuntimeError('local node exited: ' + (home / 'node.log').read_text()[-4000:])
                try:
                    request = urllib.request.Request(f'http://127.0.0.1:{rpc_port}',
                        json.dumps(dict(jsonrpc='2.0', id='test', method='status', params={})).encode(),
                        {'Content-Type': 'application/json'})
                    with urllib.request.urlopen(request, timeout=1) as response:
                        status = json.load(response)
                    if status['result']['sync_info']['latest_block_height'] >= height + 2:
                        break
                except (OSError, KeyError):
                    pass
                time.sleep(.2)
            else:
                raise RuntimeError('local chain did not advance: ' + (home / 'node.log').read_text()[-4000:])
        finally:
            node.terminate()
            try: node.wait(timeout=15)
            except subprocess.TimeoutExpired:
                node.kill()
                node.wait()
            log.close()
        output = home / 'request.json'
        env = os.environ.copy()
        env.update(SAFE_NEAR_HISTORY_OUTPUT=str(output), SAFE_NEAR_HISTORY_HEIGHT=str(height),
                   SAFE_NEAR_HISTORY_SHARD='0')
        process = subprocess.run([str(neard), '--home', str(home), 'view-state', 'apply-range',
                                  '--start-index', str(height), '--end-index', str(height),
                                  '--shard-id', '0', '--storage', 'trie-free', 'sequential'],
                                 env=env, capture_output=True, text=True)
        if process.returncode:
            raise RuntimeError(process.stderr[-6000:])
        request, archive = read(output), read(output.with_suffix('.archive.json'))
        verified = execute(replay, dict(request=request, archive=archive))
        assert verified['archiveVerified'] is True
        assert verified['observations'] == request['nativeExpected']
        mutations = ('blockHash', 'chunkHeader', 'nextBlockHeader', 'outcomes', 'outgoingReceipts')
        for field in mutations:
            changed = copy.deepcopy(archive)
            changed[field] = '1' * 32 if field == 'blockHash' else '00'
            try: execute(replay, dict(request=request, archive=changed))
            except ValueError: pass
            else: raise AssertionError(f'corrupt archived {field} was accepted')
        # Even with a full valid native/archive round trip, a local node must not
        # become a mainnet/testnet historical bundle.
        try: validate_capture(request, archive)
        except ValueError as e:
            assert 'mainnet or testnet' in str(e)
        else: raise AssertionError('local archive was accepted as public history')
        evidence = dict(localnetArchiveRoundTrip=True, publicHistoricalReplayEstablished=False,
                        blockHeight=height, stateRoot=archive['stateRoot'],
                        archiveMutationsRejected=len(mutations))
        report = HERE.parents[1] / 'audit/history-localnet-export.json'
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(json.dumps(evidence, indent=2) + '\n')
        print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
