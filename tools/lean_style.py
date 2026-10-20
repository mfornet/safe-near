#!/usr/bin/env python3
"""Check Lean source style, or apply Mathlib's automatic style fixes with --fix."""

import argparse
from pathlib import Path
import subprocess

from check_lean_toolchains import repository_files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fix", action="store_true")
    parser.add_argument("files", nargs="*", type=Path,
                        help="repository-relative files (default: every owned .lean file)")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    owned = {p for p in repository_files(root) if p.suffix == ".lean" and (root / p).is_file()}
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
    return subprocess.run(command, cwd=root / "near-lean/wasm").returncode


if __name__ == "__main__":
    raise SystemExit(main())
