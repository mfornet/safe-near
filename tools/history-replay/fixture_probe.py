#!/usr/bin/env python3
"""Replay a frozen public chunk and require corrupted protocol inputs to fail."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile

from history import HERE, read, verify
from probe import scheduler_time_offset

DEFAULT = HERE / 'fixtures/mainnet-220938800-shard11'


def native(binary, request, archive, *, success):
    result = subprocess.run([str(binary)], input=json.dumps(dict(request=request, archive=archive)),
                            text=True, capture_output=True)
    if success:
        if result.returncode:
            raise AssertionError(result.stderr[-6000:])
        observed = json.loads(result.stdout)
        assert observed['archiveVerified'] is True
        assert observed['observations'] == request['nativeExpected']
    elif result.returncode == 0:
        raise AssertionError('corrupted historical input unexpectedly passed native verification')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=DEFAULT)
    parser.add_argument('--replay', type=Path)
    args = parser.parse_args()
    binary = (args.replay or Path(read(HERE / 'target/build.json')['replay'])).resolve()
    # Relocate the frozen bundle. Native replay has no access to the capture home.
    with tempfile.TemporaryDirectory(prefix='safe-near-public-replay-') as temporary:
        relocated = Path(temporary)
        for name in ('request.json', 'archive.json', 'capture-build.json', 'manifest.json'):
            (relocated / name).write_bytes((args.bundle / name).read_bytes())
        evidence = verify(relocated, binary)
        request, archive = read(relocated / 'request.json'), read(relocated / 'archive.json')
        rejected = []
        for mutation in ('missing-witness', 'incoming-receipts', 'timestamp', 'outcomes',
                         'archive-state', 'archive-block', 'successor-header', 'deterministic-stats'):
            changed, anchor = copy.deepcopy(request), copy.deepcopy(archive)
            if mutation == 'missing-witness':
                changed['witness'] = '0000000000'
            elif mutation == 'incoming-receipts':
                changed['incomingReceipts'] = '00000000'
            elif mutation == 'timestamp':
                changed['context']['blockTimestamp'] += 1
            elif mutation == 'outcomes':
                value = bytearray.fromhex(changed['nativeExpected']['outcomes'])
                value[-1] ^= 1
                changed['nativeExpected']['outcomes'] = value.hex()
            elif mutation == 'archive-state':
                anchor['stateRoot'] = '11111111111111111111111111111111'
            elif mutation == 'archive-block':
                anchor['blockHash'] = '11111111111111111111111111111111'
            elif mutation == 'successor-header':
                value = bytearray.fromhex(anchor['nextBlockHeader'])
                # Keep valid Borsh; break the successor's actual previous-hash link.
                value[1] ^= 1
                anchor['nextBlockHeader'] = value.hex()
            else:
                value = bytearray.fromhex(changed['captureTelemetry']['originalStats'])
                value[scheduler_time_offset(value) - 8] ^= 1
                changed['captureTelemetry']['originalStats'] = value.hex()
            native(binary, changed, anchor, success=False)
            rejected.append(mutation)
        telemetry = copy.deepcopy(request)
        value = bytearray.fromhex(telemetry['captureTelemetry']['originalStats'])
        offset = scheduler_time_offset(value)
        value[offset:offset + 16] = (987654321).to_bytes(16, 'little')
        telemetry['captureTelemetry'].update(originalStats=value.hex(),
                                             bandwidthSchedulerTimeToRunMs='987654321')
        native(binary, telemetry, archive, success=True)
    print(json.dumps(dict(blockHash=archive['blockHash'], blockHeight=archive['blockHeight'],
        shardId=archive['shardId'], historicalReplayEstablished=True, leanExecutionEstablished=False,
        verification=evidence, relocatedBundleVerified=True, rejectedMutations=rejected,
        changedWallClockTelemetryVerified=True), indent=2))


if __name__ == '__main__':
    main()
