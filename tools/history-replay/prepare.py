#!/usr/bin/env python3
"""Build isolated, pinned nearcore instrumentation and the offline replay binary."""
from __future__ import annotations
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REVISION = json.loads((ROOT / 'near-lean/runtime/reference.json').read_text())['revision']
LIB = 'runtime/runtime/src/lib.rs'
TRIE = 'core/store/src/trie/mod.rs'
CHAIN = 'chain/chain/src/runtime/mod.rs'
MANIFEST = 'runtime/runtime/Cargo.toml'
VIEWER = 'tools/state-viewer/src/apply_chain_range.rs'


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f'pinned overlay seam changed: {old[:80]!r}')
    return source.replace(old, new, 1)


def overlays(source):
    """Every replacement is guarded against the exact upstream content."""
    read = lambda p: (source / p).read_text()
    lib = read(LIB) + '\n#[path = "safe_near_history.rs"]\npub mod historical_capture;\n'
    trie = replace_once(read(TRIE), '    pub fn has_flat_storage_chunk_view(&self) -> bool {',
        '    pub fn historical_flat_costs(&self) -> bool { !self.use_access_tracker }\n\n'
        '    pub fn historical_map_storage(&mut self, wrap: impl FnOnce(Arc<dyn TrieStorage>) -> Arc<dyn TrieStorage>) -> Arc<dyn TrieStorage> {\n'
        '        assert!(self.memtries.is_none() && self.flat_storage_chunk_view.is_none(), "capture requires trie-free storage");\n'
        '        self.storage = wrap(self.storage.clone()); self.storage.clone()\n'
        '    }\n\n'
        '    pub fn has_flat_storage_chunk_view(&self) -> bool {')
    chain = replace_once(read(CHAIN), '.runtime\n            .apply(', '.runtime\n            .apply_historical_capture(')
    viewer = replace_once(read(VIEWER),
        '    // Apply the chunk (consumes input)\n    let apply_result = apply_chunk_from_input(input, &*runtime_adapter);',
        '    let history_input = std::env::var_os("SAFE_NEAR_HISTORY_OUTPUT").map(|_| input.clone());\n'
        '    // Apply the chunk (consumes input)\n    let apply_result = apply_chunk_from_input(input, &*runtime_adapter);\n'
        '    if let Some(input) = history_input { safe_near_history_anchor(&input, &read_store, genesis, &apply_result); }')
    viewer += '\n' + (HERE / 'archive.rs').read_text()
    manifest = read(MANIFEST) + ('\n[[bin]]\nname = "safe-near-history-replay"\npath = "safe_near_history_replay.rs"\n'
        '\n[[bin]]\nname = "safe-near-history-smoke"\npath = "safe_near_history_smoke.rs"\n'
        'required-features = ["test_features", "estimator"]\n')
    runtime = (HERE / 'runtime.rs').read_text().replace('use node_runtime::{', 'use crate::{')
    return {LIB: lib, TRIE: trie, CHAIN: chain, MANIFEST: manifest, VIEWER: viewer,
            'runtime/runtime/src/safe_near_history.rs': runtime,
            'runtime/runtime/safe_near_history_replay.rs': (HERE / 'replay.rs').read_text(),
            'runtime/runtime/safe_near_history_smoke.rs': (HERE / 'smoke.rs').read_text()}


def git(source, *args):
    return subprocess.check_output(['git', '-C', str(source), *args], text=True).strip()


def prepare(destination, source=None):
    if source and source.resolve() == destination.resolve():
        raise ValueError('instrumentation checkout must be separate from the supplied source')
    if not destination.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source:
            if git(source, 'rev-parse', 'HEAD') != REVISION or git(source, 'status', '--porcelain'):
                raise ValueError('source must be clean and exactly pinned')
            subprocess.run(['git', 'clone', '--quiet', '--shared', str(source), str(destination)], check=True)
        else:
            subprocess.run(['git', 'init', '--quiet', str(destination)], check=True)
            subprocess.run(['git', '-C', str(destination), 'fetch', '--depth=1',
                            'https://github.com/near/nearcore', REVISION], check=True)
        subprocess.run(['git', '-C', str(destination), 'checkout', '--quiet', '--detach', REVISION], check=True)
    if git(destination, 'rev-parse', 'HEAD') != REVISION:
        raise ValueError('instrumentation checkout revision mismatch')
    marker = destination / '.git/safe-near-history-overlay.json'
    if marker.exists():
        previous = json.loads(marker.read_text())
        # Refuse to overwrite local edits, including edits to our previous overlay.
        for name, digest in previous.items():
            p = destination / name
            if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != digest:
                raise ValueError(f'owned overlay changed: {name}')
        changed = set(git(destination, 'diff', '--name-only', 'HEAD').splitlines())
        untracked = set(git(destination, 'ls-files', '--others', '--exclude-standard').splitlines())
        if changed | untracked != set(previous):
            raise ValueError('instrumentation checkout has unrelated edits')
        for name in previous:
            p = destination / name
            original = subprocess.run(['git', '-C', str(destination), 'show', f'{REVISION}:{name}'], capture_output=True)
            if original.returncode == 0: p.write_bytes(original.stdout)
            else: p.unlink()
    elif git(destination, 'status', '--porcelain'):
        raise ValueError('unrecognized instrumentation checkout modifications')
    overlay = overlays(destination)
    hashes = {}
    for name, value in overlay.items():
        (destination / name).write_text(value)
        hashes[name] = hashlib.sha256(value.encode()).hexdigest()
    marker.write_text(json.dumps(hashes, indent=2) + '\n')
    return hashes


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', type=Path, help='clean cached checkout at the pinned revision')
    p.add_argument('--checkout', type=Path, default=HERE / '.nearcore' / REVISION)
    p.add_argument('--target-dir', type=Path)
    p.add_argument('--neard', action='store_true', help='also build the archive capture tool')
    p.add_argument('--smoke', action='store_true', help='also build the synthetic witness regression tool')
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    checkout = args.checkout.resolve()
    checkout.parent.mkdir(parents=True, exist_ok=True)
    lock = (checkout.parent / (checkout.name + '.history-build.lock')).open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    hashes = prepare(checkout, args.source.resolve() if args.source else None)
    adapter = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    target = (args.target_dir or checkout / 'target').resolve()
    env = os.environ.copy()
    env.update(CARGO_TARGET_DIR=str(target), SAFE_NEAR_HISTORY_ADAPTER_SHA256=adapter)
    env.setdefault('CARGO_BUILD_JOBS', '2')
    operation = 'check' if args.check else 'build'
    command = ['cargo', '+1.93.0', operation, '--locked', '-p', 'node-runtime',
               '--bin', 'safe-near-history-replay']
    subprocess.run(command, cwd=checkout, env=env, check=True)
    if args.neard:
        subprocess.run(['cargo', '+1.93.0', operation, '--locked', '-p', 'neard', '--bin', 'neard'],
                       cwd=checkout, env=env, check=True)
    if args.smoke:
        subprocess.run(['cargo', '+1.93.0', operation, '--locked', '-p', 'node-runtime', '--bin',
                        'safe-near-history-smoke', '--features', 'test_features,estimator,near-crypto/rand'],
                       cwd=checkout, env=env, check=True)
    metadata = dict(sourceRevision=REVISION, overlaySha256=hashes, adapterSha256=adapter,
                    checkout=str(checkout), replay=str(target / 'debug/safe-near-history-replay'),
                    neard=str(target / 'debug/neard') if args.neard else None, checkOnly=args.check)
    metadata['cargoLockSha256'] = hashlib.sha256((checkout / 'Cargo.lock').read_bytes()).hexdigest()
    if git(checkout, 'diff', '--name-only', 'HEAD', '--', 'Cargo.lock'):
        raise ValueError('pinned Cargo.lock changed during build')
    metadata['smoke'] = str(target / 'debug/safe-near-history-smoke') if args.smoke else None
    for label in ('replay', 'neard', 'smoke'):
        if metadata[label] and not args.check:
            with Path(metadata[label]).open('rb') as executable:
                metadata[label + 'BinarySha256'] = hashlib.file_digest(executable, 'sha256').hexdigest()
    for name, expected in hashes.items():
        if hashlib.sha256((checkout / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f'instrumentation changed during build: {name}')
    (HERE / 'target').mkdir(exist_ok=True)
    (HERE / 'target/build.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps(metadata, indent=2))


if __name__ == '__main__':
    main()
