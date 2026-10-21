#!/usr/bin/env python3
"""Capture one archived shard chunk; verify and replay a portable offline bundle."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
REVISION = '44f7ae6cd7ef08bab604e20a473bf77e35d4c993'
FILES = ('request.json', 'archive.json', 'capture-build.json')
COMPARISON_SCOPE = {'statsEncoding': 'ChunkApplyStatsV1 Borsh with time_to_run_ms zeroed',
                    'excludedTelemetry': ['stats.bandwidth_scheduler.time_to_run_ms'],
                    'originalStats': 'request.captureTelemetry.originalStats'}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON key: {key}')
        result[key] = value
    return result


def loads(data):
    return json.loads(data, object_pairs_hook=unique_object)


def read(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError(f'expected ordinary file: {path}')
    return loads(path.read_bytes())


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for data in iter(lambda: f.read(1024 * 1024), b''):
            h.update(data)
    return h.hexdigest()


def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')


def execute(binary, payload, *, metadata=False):
    result = subprocess.run([str(binary), *(['--metadata'] if metadata else [])],
                            input=None if metadata else json.dumps(payload),
                            capture_output=True, text=True)
    if result.returncode:
        raise ValueError(f'{binary.name} exited {result.returncode}: {result.stderr[-6000:]}')
    return loads(result.stdout)


def validate_capture(request, archive):
    if request.get('format') != 'safe-near-runtime-witness-v1' or request.get('sourceRevision') != REVISION:
        raise ValueError('unknown runtime capture format or revision')
    required = {'format', 'sourceRevision', 'context', 'preStateRoot', 'flatStorageCosts',
                'validatorAccountsUpdate', 'transactions', 'transactionValidity', 'incomingReceipts',
                'epochQueries', 'witness', 'nativeExpected', 'captureTelemetry'}
    if set(request) != required:
        raise ValueError('missing or unknown runtime capture fields')
    if (archive.get('format') != 'safe-near-archive-anchor-v1'
            or archive.get('archiveComparisonEstablished') is not True):
        raise ValueError('capture lacks an archive comparison')
    c, expected = request['context'], request['nativeExpected']
    for field in ('blockHeight', 'shardId'):
        if type(c[field]) is not int or c[field] != archive[field]:
            raise ValueError(f'archive {field} differs from runtime input')
    if request['epochQueries'].get('chain_id') != archive['chainId']:
        raise ValueError('archive network differs from epoch environment')
    if archive['chainId'] not in ('mainnet', 'testnet'):
        raise ValueError('historical fixture must come from mainnet or testnet')
    for field in ('stateRoot', 'outcomeRoot', 'outcomes', 'outgoingReceipts', 'gasBurnt', 'balanceBurnt'):
        if archive[field] != expected[field]:
            raise ValueError(f'archive {field} differs from native execution')
    if request['validatorAccountsUpdate'] is not None or c['isNewChunk'] is not True:
        raise ValueError('first fixture requires a new chunk without epoch account updates')


def replay(request, archive, binary):
    metadata = execute(binary, None, metadata=True)
    if metadata.get('sourceRevision') != REVISION:
        raise ValueError('offline executable is not at the pinned nearcore revision')
    result = execute(binary, {'request': request, 'archive': archive})
    if result.get('archiveVerified') is not True or result.get('observations') != request['nativeExpected']:
        raise ValueError('native archive verification or complete offline output comparison failed')
    return dict(binarySha256=sha(binary), metadata=metadata,
                archiveVerified=True, offlineReplayVerified=True)


def package(request_path, archive_path, build_path, destination, binary):
    assets = {}
    for source, name in zip((request_path, archive_path, build_path), FILES):
        read(source)
        assets[name] = source.read_bytes()
    request, archive, build = (loads(assets[name]) for name in FILES)
    validate_capture(request, archive)
    if build.get('sourceRevision') != REVISION or build.get('checkOnly') is not False:
        raise ValueError('capture build is missing or unbuilt')
    evidence = replay(request, archive, binary)
    # Reserve the destination exclusively. A manifest is written last; partial
    # publication is never accepted by verify(). Existing paths are never replaced.
    destination.mkdir()
    try:
        for name, data in assets.items():
            (destination / name).write_bytes(data)
        manifest = dict(format='safe-near-historical-chunk-v1', sourceRevision=REVISION,
                        chainId=archive['chainId'], blockHash=archive['blockHash'],
                        blockHeight=archive['blockHeight'], shardId=archive['shardId'],
                        files={name: sha(destination / name) for name in FILES},
                        verification=evidence,
                        comparisonScope=COMPARISON_SCOPE,
                        trustBoundary='trusted retained nearcore store; consensus signatures are not reverified',
                        leanExecutionEstablished=False)
        write(destination / 'manifest.json', manifest)
    except BaseException:
        shutil.rmtree(destination)
        raise
    return manifest


def verify(directory, binary, model=None):
    manifest = read(directory / 'manifest.json')
    if manifest.get('format') != 'safe-near-historical-chunk-v1' or manifest.get('sourceRevision') != REVISION:
        raise ValueError('unknown historical bundle format or revision')
    if set(manifest.get('files', {})) != set(FILES):
        raise ValueError('historical bundle assets are incomplete or unknown')
    if manifest.get('comparisonScope') != COMPARISON_SCOPE:
        raise ValueError('unknown deterministic output comparison scope')
    for name, expected in manifest['files'].items():
        path = directory / name
        read(path)  # Includes symlink and duplicate-key rejection.
        if sha(path) != expected:
            raise ValueError(f'asset hash mismatch: {name}')
    request, archive = read(directory / 'request.json'), read(directory / 'archive.json')
    validate_capture(request, archive)
    for key in ('chainId', 'blockHash', 'blockHeight', 'shardId'):
        if manifest[key] != archive[key]:
            raise ValueError(f'manifest {key} does not identify its archive')
    result = replay(request, archive, binary)
    if model:
        # The candidate consumes the witness request, never nativeExpected. Its
        # protocol output must use the same canonical observation encoding.
        model_request = {k: v for k, v in request.items() if k not in ('nativeExpected', 'captureTelemetry')}
        observed = execute(model, model_request)
        if observed != request['nativeExpected']:
            raise ValueError('candidate output differs from historical native observations')
        result.update(modelSha256=sha(model), leanExecutionEstablished=True)
    return result


def capture(args):
    if args.out.exists():
        raise ValueError('capture destination already exists')
    build = read(args.build)
    if not build.get('neard') or Path(build['neard']).resolve() != args.neard.resolve():
        raise ValueError('capture executable does not match the recorded instrumentation build')
    if sha(args.neard) != build.get('neardBinarySha256'):
        raise ValueError('capture executable bytes differ from build provenance')
    if not args.near_home.is_dir():
        raise ValueError('archival nearcore home directory does not exist')
    with tempfile.TemporaryDirectory(prefix='safe-near-history-') as tmp:
        stage = Path(tmp)
        output = stage / 'request.json'
        env = os.environ.copy()
        env.update(SAFE_NEAR_HISTORY_OUTPUT=str(output), SAFE_NEAR_HISTORY_HEIGHT=str(args.height),
                   SAFE_NEAR_HISTORY_SHARD=str(args.shard_id))
        command = [str(args.neard), '--home', str(args.near_home.resolve()), 'view-state',
                   '-t', args.temperature, 'apply-range', '--start-index', str(args.height),
                   '--end-index', str(args.height), '--shard-id', str(args.shard_id),
                   '--storage', 'trie-free', 'sequential']
        # No --readwrite, --save-state or --save-state-transitions: archive data is read-only.
        subprocess.run(command, env=env, check=True)
        if sha(args.neard) != build['neardBinarySha256']:
            raise ValueError('capture executable changed during execution')
        if not output.exists() or not output.with_suffix('.archive.json').exists():
            raise ValueError('requested historical chunk was skipped or archive export did not complete')
        return package(output, output.with_suffix('.archive.json'), args.build, args.out, args.replay)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    commands = p.add_subparsers(dest='command', required=True)
    cap = commands.add_parser('capture')
    cap.add_argument('--near-home', type=Path, required=True)
    cap.add_argument('--height', type=int, required=True)
    cap.add_argument('--shard-id', type=int, required=True)
    cap.add_argument('--temperature', choices=('hot', 'cold'), default='hot')
    cap.add_argument('--neard', type=Path, required=True)
    cap.add_argument('--build', type=Path, default=HERE / 'target/build.json')
    cap.add_argument('--replay', type=Path, required=True)
    cap.add_argument('--out', type=Path, required=True)
    check = commands.add_parser('verify')
    check.add_argument('bundle', type=Path)
    check.add_argument('--replay', type=Path, required=True)
    check.add_argument('--model', type=Path)
    args = p.parse_args()
    if args.command == 'capture':
        result = capture(args)
    else:
        result = verify(args.bundle, args.replay, args.model)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
