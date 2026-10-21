#!/usr/bin/env python3
"""Exercise real native capture/replay with synthetic inputs; no historical claim."""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile

from history import read

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def run(binary, request, env=None, success=True):
    p = subprocess.run([str(binary)], input=json.dumps(request), text=True,
                       capture_output=True, env=env)
    if success and p.returncode:
        raise AssertionError(p.stderr[-6000:])
    if not success:
        if p.returncode == 0:
            raise AssertionError('corrupt witness unexpectedly replayed successfully')
        return None
    return json.loads(p.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True, help='existing full-runtime oracle, for --example')
    parser.add_argument('--build', type=Path, default=HERE / 'target/build.json')
    args = parser.parse_args()
    build = read(args.build)
    smoke, replay = Path(build['smoke']), Path(build['replay'])
    original = json.loads(subprocess.check_output([str(args.reference), '--example']))
    cases = []
    for protocol in (83, 84, 85, 86):
        for kind in ('transfer', 'expired', 'write', 'missing-method'):
            for flat in (False, True):
                request = copy.deepcopy(original)
                request.update(protocolVersion=protocol, flatStorageCosts=flat)
                if kind == 'expired':
                    request['transactionValidity'] = [False]
                if kind in ('write', 'missing-method'):
                    request['code'] = list((ROOT / 'tools/chain-conformance/fixtures/storage_lifecycle.wasm').read_bytes())
                    request['method'] = 'write' if kind == 'write' else 'absent'
                with tempfile.TemporaryDirectory() as tmp:
                    output = Path(tmp) / 'request.json'
                    env = os.environ.copy()
                    env.update(SAFE_NEAR_HISTORY_OUTPUT=str(output),
                               SAFE_NEAR_HISTORY_HEIGHT=str(request['blocks'][0]['blockHeight']),
                               SAFE_NEAR_HISTORY_SHARD='0')
                    expected = run(smoke, request, env)
                    witness = read(output)
                    assert run(replay, witness) == expected
                    assert witness['transactionValidity'] == ([False] if kind == 'expired' else [True])
                    assert witness['flatStorageCosts'] == flat
                    for mutation in ('missing-nodes', 'expected-root', 'config', 'validity', 'missing-epoch'):
                        changed = copy.deepcopy(witness)
                        if mutation == 'missing-nodes':
                            changed['witness'] = '0000000000'  # PartialState::TrieValues([])
                        elif mutation == 'expected-root':
                            changed['nativeExpected']['stateRoot'] = '1' * 32
                        elif mutation == 'config':
                            changed['context']['runtimeConfig'] = 'different'
                        elif mutation == 'validity':
                            changed['transactionValidity'][0] = not changed['transactionValidity'][0]
                        else:
                            changed['epochQueries'] = {}
                        run(replay, changed, success=False)
                    cases.append(dict(protocol=protocol, kind=kind, flatStorageCosts=flat,
                                      mutationsRejected=5, witnessBytes=len(bytes.fromhex(witness['witness']))))
    report = dict(historicalReplayEstablished=False, syntheticWitnessRoundTrips=len(cases), cases=cases)
    destination = ROOT / 'audit/history-witness-smoke.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
