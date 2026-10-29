#!/usr/bin/env python3
"""Require every repository-owned Lake package to use the root Lean pin."""

import argparse
from pathlib import Path
import re
import subprocess
import sys


def repository_files(root: Path) -> list[Path]:
    """Include new local files, but never descend into submodules or ignored builds."""
    result = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=root, check=True, stdout=subprocess.PIPE,
    )
    return sorted({Path(p.decode()) for p in result.stdout.split(b"\0") if p})


def changed_files(root: Path, revision: str) -> set[Path]:
    """Files that differ from `revision` in the working tree, deletions excluded."""
    result = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=d", "-z", revision],
        cwd=root, check=True, stdout=subprocess.PIPE,
    )
    return {Path(p.decode()) for p in result.stdout.split(b"\0") if p}


def check(root: Path) -> list[str]:
    canonical = root / "lean-toolchain"
    if not canonical.is_file():
        return ["missing canonical lean-toolchain at repository root"]
    expected = canonical.read_text().strip()
    if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", expected):
        return [f"lean-toolchain must pin a Lean release, got {expected!r}"]
    files = repository_files(root)
    packages = {p.parent for p in files if p.name in {"lakefile.toml", "lakefile.lean"}
                and (root / p).is_file()}
    pins = {p for p in files if p.name == "lean-toolchain" and (root / p).is_file()}
    pins |= {p / "lean-toolchain" for p in packages}
    errors = []
    for pin in sorted(pins):
        path = root / pin
        if not path.is_file():
            errors.append(f"{pin}: missing toolchain pin (expected {expected})")
        elif path.read_text().strip() != expected:
            errors.append(f"{pin}: expected {expected}, got {path.read_text().strip()!r}")
    if not packages:
        errors.append("no repository-owned Lake packages found")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    errors = check(args.root)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print("All repository-owned Lean packages match the root lean-toolchain.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
