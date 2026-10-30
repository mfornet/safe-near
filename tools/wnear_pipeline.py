"""Shared lock and phase timing for the wNEAR validation pipeline."""
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / 'contracts/w-near/verification/.lake/build/blueprint'
LOCK = WORK / 'pipeline.lock'
FD_ENV = 'WNEAR_PIPELINE_LOCK_FD'


@contextmanager
def pipeline_lock():
    WORK.mkdir(parents=True, exist_ok=True)
    inherited = os.environ.get(FD_ENV)
    if inherited is not None:
        fd = int(inherited)
        stat = os.fstat(fd)
        expected = LOCK.stat()
        if (stat.st_dev, stat.st_ino) != (expected.st_dev, expected.st_ino):
            raise RuntimeError('Inherited wNEAR lock does not match this checkout')
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        yield fd
    else:
        with LOCK.open('a') as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            yield handle.fileno()


def record_phase(name, seconds, **details):
    WORK.mkdir(parents=True, exist_ok=True)
    record = {'at': datetime.now(timezone.utc).isoformat(timespec='seconds'),
              'phase': name, 'seconds': round(seconds, 3), **details}
    with (WORK / 'timings.jsonl').open('a') as log:
        log.write(json.dumps(record) + '\n')
    print('wNEAR timing: ' + json.dumps(record), flush=True)


def timed_run(name, command, *, cwd=ROOT, pass_fds=(), env=None):
    start = time.monotonic()
    try:
        subprocess.run(command, cwd=cwd, check=True, pass_fds=pass_fds, env=env)
    finally:
        record_phase(name, time.monotonic() - start)
