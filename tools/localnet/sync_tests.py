#!/usr/bin/env python3
"""Header sync and the sync block on the in-memory network (M7): `just node-sync-tests`.

Unpacks `near-lean/node/corpus/blocks` as `chain_apply.py` does and runs `node-sync-tests` on each topology: a client
node syncs the headers and bodies of the localnet chain from a server node over the in-memory network, and the tests
of a changed header, a missing header and a changed body.  Exits 0 only when all of them pass.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import chain_apply
import chain_corpus

BINARY = chain_corpus.ROOT / "near-lean/node/.lake/build/bin/node-sync-tests"
LINE = re.compile(r"(\d+) checks, (\d+) failures")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--corpus", type=Path, default=chain_corpus.DEFAULT_CORPUS)
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("topologies", nargs="*", default=list(chain_corpus.TOPOLOGIES))
    a = parser.parse_args()
    problems = chain_corpus.check(a.corpus)
    if problems:
        print("\n".join(problems), file=sys.stderr)
        sys.exit(1)
    ok = True
    checks = 0
    with tempfile.TemporaryDirectory(prefix="safe-near-sync-") as temporary:
        for topology in a.topologies:
            directory = chain_apply.unpack(a.corpus, Path(temporary), topology)
            result = subprocess.run([str(a.binary), str(directory), str(chain_corpus.ROOT / "near-lean/vm/configs")],
                                    text=True, capture_output=True)
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
            match = LINE.search(result.stdout)
            if result.returncode != 0 or not match or int(match.group(2)) != 0:
                ok = False
            if match:
                checks += int(match.group(1))
    print(f"node-sync-tests: {checks} checks, " + ("all pass" if ok else "FAILED"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
