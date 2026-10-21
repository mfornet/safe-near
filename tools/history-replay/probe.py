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


def scheduler_time_offset(stats):
    """Locate the one excluded field in the pinned ChunkApplyStatsV1 encoding.

    Decode only its Borsh prefix, including variable-sized maps. Mutations below
    prove that duration can vary while adjacent deterministic stats remain bound.
    """
    offset = 33  # height, shard, is_new_chunk, transaction/receipt counts
    def count():
        nonlocal offset
        value = int.from_bytes(stats[offset:offset + 4], 'little')
        offset += 4
        return value
    for entry_size in (24, 40, 40, 40, 9):
        entries = count()
        offset += entries * entry_size
    offset += 1  # all_outgoing_metadatas_ready
    present = stats[offset]
    assert present in (0, 1)
    offset += 1 + 40 * present  # optional scheduler parameters
    for _ in range(count()):
        offset += 16  # source/destination shards
        entries = count()
        offset += entries * 8
    offset += 8  # previous request count
    assert offset + 16 <= len(stats)
    return offset


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
                    telemetry_variant = copy.deepcopy(witness)
                    stats = bytearray.fromhex(witness['captureTelemetry']['originalStats'])
                    offset = scheduler_time_offset(stats)
                    stats[offset:offset + 16] = (1234567890123).to_bytes(16, 'little')
                    telemetry_variant['captureTelemetry'].update(
                        originalStats=stats.hex(), bandwidthSchedulerTimeToRunMs='1234567890123')
                    assert run(replay, telemetry_variant) == expected
                    stats[offset - 8] ^= 1  # adjacent deterministic scheduler counter
                    telemetry_variant['captureTelemetry']['originalStats'] = stats.hex()
                    run(replay, telemetry_variant, success=False)
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
                                      mutationsRejected=6, telemetryVariantsMatched=1,
                                      witnessBytes=len(bytes.fromhex(witness['witness']))))
    report = dict(historicalReplayEstablished=False, syntheticWitnessRoundTrips=len(cases), cases=cases)
    destination = ROOT / 'audit/history-witness-smoke.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
