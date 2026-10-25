#!/usr/bin/env python3
"""The block corpus through the Lean chain validator (M5a): `just chain-validate-corpus`.

Unpacks `near-lean/node/corpus/blocks` into a temporary directory and runs `node-chain-validate` on
each topology: every valid block must be accepted with the values nearcore derived for it, and every
invalid variant rejected with the `Error` variant nearcore returned.  Prints the counts and exits 0
only when all agree.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import chain_corpus

BINARY = chain_corpus.ROOT / "near-lean/node/.lake/build/bin/node-chain-validate"
LINE = re.compile(r"blocks (\d+)/(\d+) accepted, derived values agree on (\d+), variants (\d+)/(\d+) agree")


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
    totals = [0] * 5
    ok = True
    with tempfile.TemporaryDirectory(prefix="safe-near-chain-") as temporary:
        for topology in a.topologies:
            directory = chain_corpus.unpack(a.corpus, Path(temporary), topology)
            result = subprocess.run([str(a.binary), str(directory)], capture_output=True, text=True)
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
            match = LINE.search(result.stdout)
            if result.returncode != 0 or not match:
                ok = False
            if match:
                for i, value in enumerate(match.groups()):
                    totals[i] += int(value)
    accepted, blocks, derived, agree, variants = totals
    print(f"chain-validate-corpus: valid blocks accepted {accepted}/{blocks}, derived values agree {derived}/{blocks}, "
          f"invalid variants rejected as nearcore did {agree}/{variants}")
    ok = ok and accepted == blocks == derived and agree == variants and blocks > 0
    print("all agree" if ok else "DISAGREEMENT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
