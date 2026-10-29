#!/usr/bin/env python3
"""Check Lean source style, or apply Mathlib's automatic style fixes with --fix."""

import argparse
from pathlib import Path
import subprocess

from check_lean_toolchains import changed_files, repository_files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fix", action="store_true")
    parser.add_argument("files", nargs="*", type=Path,
                        help="repository-relative files (default: every owned .lean file)")
    parser.add_argument("--changed-from", metavar="REV",
                        help="only the owned .lean files that differ from this revision")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    owned = {p for p in repository_files(root) if p.suffix == ".lean" and (root / p).is_file()}
    if args.changed_from:
        if args.files:
            parser.error("--changed-from cannot be combined with files")
        files = sorted(owned & changed_files(root, args.changed_from))
        if not files:
            print(f"No Lean source changed since {args.changed_from}.")
            return 0
    else:
        files = sorted(set(args.files) if args.files else owned)
    if not files:
        parser.error("no Lean source files found")
    for file in files:
        if file not in owned:
            parser.error(f"not a repository-owned Lean file: {file}")
    command = ["lake", "env", "lean", "--run", str(root / "tools/LeanStyle.lean")]
    if args.fix:
        command.append("--fix")
    command.extend(str(root / file) for file in files)
    return subprocess.run(command, cwd=root / "near-lean/vm").returncode


if __name__ == "__main__":
    raise SystemExit(main())
