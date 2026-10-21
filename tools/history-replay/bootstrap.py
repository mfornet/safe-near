#!/usr/bin/env python3
"""Acquire recent shard state from peers with explicit time and disk limits.

This starts a non-validator, tracks one account's shard and stops after sync.
The resulting retained database can feed history.py capture. No fixture is
published here: successful synchronization is not historical replay evidence.
"""
from __future__ import annotations
import argparse
import fcntl
import json
import os
from pathlib import Path
import socket
import signal
import subprocess
import sys
import time
import urllib.request

from history import HERE, REVISION, read, sha, write

MARKER = 'safe-near-history-bootstrap.json'
NETWORK_OVERLAY = 'chain/network/src/peer_manager/peer_manager_actor.rs'


def rpc(url, method, params, timeout=10):
    request = urllib.request.Request(url, json.dumps(dict(jsonrpc='2.0', id='history-bootstrap',
        method=method, params=params)).encode(), {'Content-Type': 'application/json'})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        value = json.load(response)
    if 'error' in value:
        raise ValueError(f'RPC {method}: {value["error"]}')
    return value['result']


def boot_peers(network):
    active = {p['id']: p.get('addr') for p in network['active_peers']}
    producers = {p['peer_id'] for p in network.get('known_producers', [])}
    preferred = [f'{pid}@{addr}' for pid, addr in active.items() if addr and pid in producers]
    others = [f'{pid}@{addr}' for pid, addr in active.items() if addr and pid not in producers]
    return (preferred + others)[:20]


def free_port():
    with socket.socket() as listener:
        listener.bind(('127.0.0.1', 0))
        return listener.getsockname()[1]


def initialized_and_synced(status, genesis_height):
    sync = status.get('sync_info', {})
    # A fresh node reports syncing=false before discovering peers. That is not success.
    return sync.get('syncing') is False and sync.get('latest_block_height', genesis_height) > genesis_height


def directory_bytes(directory):
    total = 0
    for path in directory.rglob('*'):
        try:
            if path.is_file(): total += path.stat().st_size
        except FileNotFoundError:
            pass  # RocksDB can remove temporary files during traversal.
    return total


def initialize(home, neard, account, peers, build):
    home.mkdir()
    write(home / MARKER, dict(format='safe-near-history-bootstrap-v1', chainId='mainnet',
                             accountId=account, sourceRevision=REVISION,
                             captureBinarySha256=build['neardBinarySha256']))
    with (home / 'init.log').open('w') as log:
        subprocess.run([str(neard), '--home', str(home), 'init', '--chain-id', 'mainnet',
                        '--download-genesis', '--download-config', 'rpc'],
                       stdout=log, stderr=log, check=True)
    config = read(home / 'config.json')
    config['rpc']['addr'] = f'127.0.0.1:{free_port()}'
    config['rpc']['enable_debug_rpc'] = True
    config['network']['addr'] = f'127.0.0.1:{free_port()}'
    config['network'].update(max_num_peers=12, minimum_outbound_peers=3,
                            ideal_connections_lo=8, ideal_connections_hi=10,
                            safe_set_size=5, archival_peer_connections_lower_bound=1)
    config['network']['boot_nodes'] = ','.join(peers)
    config['network']['tier1'].update(enable_inbound=False, enable_outbound=False)
    config['network']['trusted_stun_servers'] = []
    config['telemetry']['endpoints'] = []
    config['archive'] = False
    config['tracked_shards_config'] = {'Accounts': [account]}
    config['state_sync'] = {'concurrency': dict(apply=2, apply_during_catchup=1,
                                              peer_downloads=2, per_shard=2)}
    (home / 'config.json').write_text(json.dumps(config, indent=2) + '\n')


def run(args):
    home = args.near_home.resolve()
    # Lock outside the home so initialization and resume configuration are also protected.
    with home.with_name(home.name + '.bootstrap.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return run_locked(args)


def run_locked(args):
    neard = args.neard.resolve()
    build = read(args.build)
    if (build.get('sourceRevision') != REVISION or build.get('checkOnly') is not False
            or sha(neard) != build.get('neardBinarySha256')):
        raise ValueError('bootstrap requires a built, pinned capture executable')
    if args.direct_state_sync and NETWORK_OVERLAY not in build.get('overlaySha256', {}):
        raise ValueError('rebuild with --neard --direct-state-sync to use outbound state requests')
    if not args.direct_state_sync:
        raise ValueError('loopback bootstrap requires --direct-state-sync; build with the same flag')
    if args.max_seconds <= 0 or args.max_gib <= 0:
        raise ValueError('time and disk limits must be positive')
    if not 1 <= args.download_concurrency <= 16:
        raise ValueError('download concurrency must be between 1 and 16')
    if not 1 <= args.apply_concurrency <= 16:
        raise ValueError('apply concurrency must be between 1 and 16')
    protocol = rpc(args.rpc, 'EXPERIMENTAL_protocol_config', {'finality': 'final'})
    if protocol.get('chain_id') != 'mainnet':
        raise ValueError('bootstrap RPC must serve mainnet')
    if not 83 <= protocol['protocol_version'] <= 86:
        raise ValueError('live mainnet protocol is outside this capture runtime\'s supported range')
    peers = read(args.boot_peers) if args.boot_peers else boot_peers(rpc(args.rpc, 'network_info', []))
    if not isinstance(peers, list) or any(not isinstance(p, str) or '@' not in p for p in peers):
        raise ValueError('boot peers must be a JSON array of peer-id@address strings')
    if not peers:
        raise ValueError('RPC returned no usable boot peers')
    home = args.near_home.resolve()
    if home.exists():
        if not args.resume:
            raise ValueError('node directory exists; use --resume only for an owned bootstrap')
        marker = read(home / MARKER)
        if (marker.get('format') != 'safe-near-history-bootstrap-v1'
                or marker.get('accountId') != args.account
                or marker.get('chainId') != 'mainnet'
                or marker.get('sourceRevision') != REVISION
                or marker.get('captureBinarySha256') != build['neardBinarySha256']):
            raise ValueError('node directory is not the requested owned bootstrap')
        config = read(home / 'config.json')
        if config.get('archive') is not False or config.get('tracked_shards_config') != {'Accounts': [args.account]}:
            raise ValueError('owned node tracking configuration changed')
        config['network']['boot_nodes'] = ','.join(peers)
        (home / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
    else:
        initialize(home, neard, args.account, peers, build)
    if (home / 'validator_key.json').exists():
        raise ValueError('bootstrap must not have a validator signing key')
    config = read(home / 'config.json')
    config['network'].setdefault('experimental', {})['connect_only_to_boot_nodes'] = bool(args.boot_peers)
    config['network']['connect_to_reliable_peers_on_startup'] = not bool(args.boot_peers)
    config['state_sync']['concurrency'].update(peer_downloads=args.download_concurrency,
                                              per_shard=max(args.download_concurrency, args.apply_concurrency),
                                              apply=args.apply_concurrency)
    (home / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
    url = 'http://' + config['rpc']['addr']
    genesis_height = read(home / 'genesis.json')['genesis_height']
    env = os.environ.copy()
    for field in ('SAFE_NEAR_HISTORY_OUTPUT', 'SAFE_NEAR_HISTORY_HEIGHT', 'SAFE_NEAR_HISTORY_SHARD'):
        env.pop(field, None)
    if args.direct_state_sync: env['SAFE_NEAR_HISTORY_DIRECT_STATE_SYNC'] = '1'
    else: env.pop('SAFE_NEAR_HISTORY_DIRECT_STATE_SYNC', None)
    start = time.monotonic()
    synced_at = None
    reason = 'timeLimit'
    selected = None
    last_report = -30
    with (home / 'bootstrap.log').open('a') as log:
        node = subprocess.Popen([str(neard), '--home', str(home), 'run'], env=env, stdout=log, stderr=log)
        stopping = False
        def request_stop(*_):
            nonlocal stopping
            stopping = True
        previous_handlers = {sig: signal.signal(sig, request_stop)
                             for sig in (signal.SIGINT, signal.SIGTERM)}
        try:
            while time.monotonic() - start < args.max_seconds:
                if stopping or (home / 'bootstrap-stop').exists():
                    reason = 'stopRequested'
                    break
                if node.poll() is not None:
                    raise ValueError(f'node exited {node.returncode}; inspect {home / "bootstrap.log"}')
                size = directory_bytes(home)
                if size >= args.max_gib * 1024**3:
                    reason = 'diskLimit'
                    break
                try:
                    status = rpc(url, 'status', {}, timeout=2)
                    progress = dict(elapsedSeconds=round(time.monotonic() - start), bytes=size,
                                    sync=status['sync_info'])
                    try:
                        with urllib.request.urlopen(url + '/debug/api/sync_status', timeout=2) as response:
                            progress['stage'] = json.load(response)
                    except (OSError, ValueError):
                        pass
                    (home / 'bootstrap-progress.json').write_text(json.dumps(progress, indent=2) + '\n')
                    if progress['elapsedSeconds'] - last_report >= 30:
                        print(json.dumps(progress), file=sys.stderr, flush=True)
                        last_report = progress['elapsedSeconds']
                    if initialized_and_synced(status, genesis_height):
                        height = status['sync_info']['latest_block_height']
                        if synced_at is None: synced_at = height
                        if height >= synced_at + 8:
                            candidate = rpc(url, 'block', {'finality': 'final'}, timeout=2)
                            if candidate['header']['height'] > synced_at:
                                selected = candidate
                                reason = 'synced'
                                break
                    else:
                        synced_at = None
                except (OSError, ValueError, KeyError):
                    pass  # Busy header verification can temporarily delay local RPC.
                time.sleep(5)
        finally:
            node.terminate()
            try: node.wait(timeout=20)
            except subprocess.TimeoutExpired:
                node.kill()
                node.wait()
            for sig, handler in previous_handlers.items():
                signal.signal(sig, handler)
    result = dict(reason=reason, elapsedSeconds=round(time.monotonic() - start),
                  bytes=directory_bytes(home), publicHistoricalReplayEstablished=False)
    if selected:
        result['candidateBlockHash'] = selected['header']['hash']
        result['candidateBlockHeight'] = selected['header']['height']
        (home / 'candidate-block.json').write_text(json.dumps(selected, indent=2) + '\n')
    (home / 'bootstrap-result.json').write_text(json.dumps(result, indent=2) + '\n')
    if reason != 'synced':
        raise ValueError(f'bootstrap stopped at {reason}; retained state is resumable at {home}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--near-home', type=Path, required=True)
    parser.add_argument('--neard', type=Path, required=True)
    parser.add_argument('--build', type=Path, default=HERE / 'target/build.json')
    parser.add_argument('--account', default='a.near')
    parser.add_argument('--rpc', default='https://rpc.mainnet.fastnear.com')
    parser.add_argument('--boot-peers', type=Path, help='JSON array of explicit peers; connects only to these')
    parser.add_argument('--max-seconds', type=int, default=1800)
    parser.add_argument('--max-gib', type=float, default=10)
    parser.add_argument('--download-concurrency', type=int, default=2)
    parser.add_argument('--apply-concurrency', type=int, default=2)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--direct-state-sync', action='store_true')
    print(json.dumps(run(parser.parse_args()), indent=2))


if __name__ == '__main__':
    main()
