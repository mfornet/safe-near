#!/usr/bin/env python3
"""Replay every corpus chunk through the Lean runtime and compare it with what neard recorded.

For each chunk this script

1. lists the *blockers*: features of the bundle that the Lean runtime's input format or model
   cannot express (the first one becomes the ``unsupported`` reason; none is ever faked),
2. converts the bundle into a ``registered-replay`` request (``lean_input.py``) and checks that Lean
   rebuilds the chunk's complete pre-state, byte for byte, from it,
3. runs the chunk and compares the outcomes, outgoing receipts and the post-state field by field with
   the bundle's ``expected`` section (never the other way round).

Result per chunk: ``pass``, ``fail: <first differing field>`` or ``unsupported: <reason>``.
Writes ``audit/chain-replay-corpus.json``; exits 0 only if every chunk passes unless ``--report``.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor
import json
import os
from pathlib import Path
import sys
import time

import corpus
import lean_input

ROOT = corpus.ROOT
REGISTERED = ROOT / "near-lean/chain/.lake/build/bin/registered-replay"
AUDIT = ROOT / "audit/chain-replay-corpus.json"


def summarize(rows: list[dict]) -> dict:
    statuses: dict[str, int] = {}
    reasons: dict[str, int] = {}
    blockers: dict[str, int] = {}
    for row in rows:
        statuses[row["status"]] = statuses.get(row["status"], 0) + 1
        if row["status"] != "pass":
            reasons[row["detail"]] = reasons.get(row["detail"], 0) + 1
        for blocker in row.get("blockers", []):
            blockers[blocker] = blockers.get(blocker, 0) + 1
    order = lambda table: dict(sorted(table.items(), key=lambda item: (-item[1], item[0])))
    return {"chunks": len(rows), "byStatus": order(statuses), "byReason": order(reasons), "byBlocker": order(blockers)}


def replay_chunk(directory: Path, corpus_root: Path, binary: Path) -> dict:
    bundle = corpus.unpack(directory, corpus_root)
    row = {"chunk": directory.name, "tags": [t for t in corpus.tags(bundle) if t.startswith(("action:", "receipt:", "host:"))]}
    started = time.time()
    try:
        outcome = lean_input.replay(bundle, binary)
    except lean_input.Unsupported as problem:
        row.update(status="unsupported", detail=problem.reasons[0], blockers=problem.reasons)
    except lean_input.Mismatch as problem:
        row.update(status="fail", detail=problem.field, blockers=problem.blockers)
    else:
        row.update(status="pass", detail="", blockers=outcome.blockers)
    row["seconds"] = round(time.time() - started, 2)
    return row


def render(summary: dict) -> str:
    lines = [f"chain-replay-corpus: {summary['chunks']} chunks"]
    for status in ("pass", "fail", "unsupported"):
        lines.append(f"  {status:12} {summary['byStatus'].get(status, 0)}")
    if summary["byReason"]:
        lines.append("by first reason (unsupported / fail):")
        lines.extend(f"  {count:5}  {reason}" for reason, count in summary["byReason"].items())
    if summary["byBlocker"]:
        lines.append("chunks affected per blocker (all blockers of every chunk):")
        lines.extend(f"  {count:5}  {blocker}" for blocker, count in summary["byBlocker"].items())
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=corpus.DEFAULT_CORPUS)
    parser.add_argument("--binary", type=Path, default=REGISTERED)
    parser.add_argument("--report", action="store_true", help="always exit 0")
    parser.add_argument("--audit", type=Path, default=AUDIT)
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1),
                        help="chunks replayed at the same time (each is an independent Lean process)")
    parser.add_argument("chunks", nargs="*", help="restrict to these chunk names")
    arguments = parser.parse_args()
    directories = [directory for directory in corpus.chunk_dirs(arguments.corpus)
                   if not arguments.chunks or directory.name in arguments.chunks]
    if arguments.jobs > 1 and len(directories) > 1:
        # a few chunks take minutes: hand out the work one chunk at a time, keep the order of the corpus
        with ProcessPoolExecutor(max_workers=arguments.jobs) as pool:
            rows = list(pool.map(replay_chunk, directories, [arguments.corpus] * len(directories),
                                 [arguments.binary] * len(directories), chunksize=1))
    else:
        rows = [replay_chunk(directory, arguments.corpus, arguments.binary) for directory in directories]
    summary = summarize(rows)
    arguments.audit.parent.mkdir(parents=True, exist_ok=True)
    arguments.audit.write_text(json.dumps({"corpus": str(arguments.corpus.relative_to(ROOT)) if arguments.corpus.is_relative_to(ROOT) else str(arguments.corpus),
                                           "summary": summary, "chunks": rows}, indent=1, sort_keys=True) + "\n")
    print(render(summary))
    if not arguments.report and summary["byStatus"].get("pass", 0) != summary["chunks"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
