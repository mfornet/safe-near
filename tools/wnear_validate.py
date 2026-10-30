#!/usr/bin/env python3
"""Run the complete strict wNEAR checkpoint under the shared build lock."""
import os
import subprocess
import sys
from wnear_pipeline import FD_ENV, ROOT, pipeline_lock, timed_run


def main():
    with pipeline_lock() as fd:
        env = os.environ.copy()
        env[FD_ENV] = str(fd)
        common = {'pass_fds': (fd,), 'env': env}
        timed_run('near-logic-compilation', ['lake', 'build', 'NearLogic'],
                  cwd=ROOT / 'near-lean/near-logic', **common)
        timed_run('near-logic-audit', ['python3', 'tools/axiom-audit.py', 'near-lean/near-logic',
                  '--no-build', '--report', 'audit/near-logic.json'], **common)
        timed_run('wnear-compilation', ['lake', 'build', 'Model', 'Spec', 'Proofs', 'Bridge', 'Blueprint',
                  'Differential', 'runtime-adapter-tests', 'wnear-scenarios', 'wnear-harness'],
                  cwd=ROOT / 'contracts/w-near/verification', **common)
        timed_run('wnear-audit', ['python3', 'tools/axiom-audit.py', 'contracts/w-near/verification',
                  '--no-build', '--allow-sorry-module', 'Proofs.Refinement', '--report', 'audit/wnear.json',
                  '--statements', 'contracts/w-near/verification/statements.json', *sys.argv[1:]], **common)
        timed_run('frontier-check', ['python3', 'tools/wnear_blueprint.py', '--check',
                  '--audit-report', 'audit/wnear.json'], **common)


if __name__ == '__main__':
    try:
        main()
    except (subprocess.CalledProcessError, OSError, RuntimeError) as error:
        print(f'wNEAR validation failed: {error}', file=sys.stderr)
        sys.exit(1)
