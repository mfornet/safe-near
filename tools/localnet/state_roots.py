#!/usr/bin/env python3
"""State roots of the corpus through the Lean trie (M4): `just node-state-roots`.

For every chunk this writes a case file (the raw pre-state entries and root, the `stateDiff`, the
post-state root nearcore recorded and, unless `--no-replay`, the complete post-state of Lean's own
replay of the chunk) and runs `node-state-roots` on the directory. The Lean program rebuilds the
pre-state trie, applies the diff with `Trie.update` and compares the roots; with the replayed
post-state it also checks that Lean's runtime output has the state root nearcore produced.

The case format is documented in `near-lean/node/NodeConformance/StateRoots.lean`.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile

import corpus
import lean_input

ROOT = corpus.ROOT
REGISTERED = ROOT / "near-lean/chain/.lake/build/bin/registered-replay"
STATE_ROOTS = ROOT / "near-lean/node/.lake/build/bin/node-state-roots"
MAGIC = b"NSR1"


def u32(n: int) -> bytes:
    return struct.pack("<I", n)


def blob(b: bytes) -> bytes:
    return u32(len(b)) + b


def entries(rows) -> bytes:
    rows = list(rows)
    return u32(len(rows)) + b"".join(blob(k) + blob(v) for k, v in rows)


def encode_case(bundle: dict, post_state: dict[bytes, bytes] | None) -> bytes:
    """The case file of a bundle; `post_state` is Lean's replayed post-state, when available."""
    pre = bundle["preState"]
    expected = bundle["expected"]
    out = [MAGIC, bytes.fromhex(pre["root"]),
           entries((bytes.fromhex(k), bytes.fromhex(v)) for k, v in pre["entries"])]
    diff = expected["stateDiff"]
    out.append(u32(len(diff)))
    for key, value in diff:
        out.append(blob(bytes.fromhex(key)) + (b"\0" if value is None else b"\1" + blob(bytes.fromhex(value))))
    out.append(bytes.fromhex(expected["postStateRoot"]))
    if post_state is None:
        out.append(b"\0")
    else:
        out.append(b"\1" + entries(sorted(post_state.items())))
    return b"".join(out)


def make_case(directory: Path, corpus_root: Path, binary: Path, target: Path, replay: bool) -> str:
    bundle = corpus.unpack(directory, corpus_root)
    post = lean_input.replay(bundle, binary).post_state if replay else None
    (target / f"{directory.name}.case").write_bytes(encode_case(bundle, post))
    return directory.name


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--corpus", type=Path, default=corpus.DEFAULT_CORPUS)
    parser.add_argument("--no-replay", action="store_true",
                        help="skip Lean's replay of each chunk (about 15 minutes on four cores)")
    parser.add_argument("--cases-only", action="store_true",
                        help="write the case files (into --work) and stop; the store tests read them")
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--work", type=Path, help="keep the case files here (reused when present)")
    parser.add_argument("--binary", type=Path, default=REGISTERED)
    parser.add_argument("chunks", nargs="*", help="restrict to these chunk names")
    arguments = parser.parse_args()
    directories = [d for d in corpus.chunk_dirs(arguments.corpus) if not arguments.chunks or d.name in arguments.chunks]
    with tempfile.TemporaryDirectory(prefix="safe-near-state-roots-") as temporary:
        target = arguments.work or Path(temporary)
        target.mkdir(parents=True, exist_ok=True)
        todo = [d for d in directories if not (target / f"{d.name}.case").exists()]
        for stale in target.glob("*.case"):
            if stale.stem not in {d.name for d in directories}:
                stale.unlink()
        replay = not arguments.no_replay
        if todo:
            print(f"state-roots: writing {len(todo)} case files" + (" (replaying each chunk in Lean)" if replay else ""),
                  flush=True)
            with ProcessPoolExecutor(max_workers=arguments.jobs) as pool:
                list(pool.map(make_case, todo, [arguments.corpus] * len(todo), [arguments.binary] * len(todo),
                              [target] * len(todo), [replay] * len(todo), chunksize=1))
        if arguments.cases_only:
            return
        result = subprocess.run([str(STATE_ROOTS), str(target)])
        sys.exit(result.returncode)


if __name__ == "__main__":
    main()
