#!/usr/bin/env python3
"""Check or format handwritten Lean package sources with a pinned syntax formatter.

The formatter is built from immutable sources with the root Lean toolchain.
It validates candidates before publication; validation is never bypassed.
"""

import argparse
from collections import defaultdict
import fcntl
from fnmatch import fnmatchcase
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from check_lean_toolchains import changed_files, repository_files


ROOT = Path(__file__).resolve().parents[1]


def source_groups(root, requested, pin, changed=None):
    """Package sources grouped by package. `changed` narrows the default
    selection: what it excludes is skipped silently, as for a full run."""
    files = repository_files(root)
    owned = {p for p in files if p.suffix == ".lean" and (root / p).is_file()}
    if changed is not None:
        owned &= changed
        if not owned:
            return {}, []
    packages = {p.parent for p in files if p.name in {"lakefile.toml", "lakefile.lean"}
                and (root / p).is_file()}
    groups = defaultdict(list)
    skipped = []
    for path in sorted(set(requested) if requested else owned):
        if path not in owned or path.is_absolute() or ".." in path.parts:
            raise ValueError(f"not a repository-owned Lean source: {path}")
        if any(fnmatchcase(path.as_posix(), pattern) for pattern in pin["generated"]):
            if requested:
                raise ValueError(f"protected generated source: {path}")
            skipped.append(path)
            continue
        package = next((parent for parent in path.parents if parent in packages), None)
        if package is None:
            if requested:
                raise ValueError(f"source is outside a Lake package (use lean-lint): {path}")
            skipped.append(path)
            continue
        groups[package].append(path.relative_to(package))
    if not groups and changed is None:
        raise ValueError("no handwritten Lean package sources selected")
    return dict(sorted(groups.items())), skipped


def formatter(root=ROOT):
    pin = json.loads((root / "tools/lean_format_tool.json").read_text())
    revision = pin["revision"]
    if len(revision) != 40 or any(c not in "0123456789abcdef" for c in revision):
        raise ValueError("formatter revision must be an immutable Git commit")
    toolchain = (root / "lean-toolchain").read_text().strip()
    key = revision + "-" + hashlib.sha256(toolchain.encode()).hexdigest()[:12]
    cache = root / "near-lean/.lake/lean-fmt"
    cache.mkdir(parents=True, exist_ok=True)
    source = cache / key
    # Serialize initialization/builds across local invocations. Never reset or
    # repair an existing checkout behind another process's back.
    with (cache / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not source.exists():
            with tempfile.TemporaryDirectory(prefix=".fetch-", dir=cache) as temporary:
                staging = Path(temporary) / "source"
                staging.mkdir()
                subprocess.run(["git", "init", "--quiet", str(staging)], check=True)
                subprocess.run(["git", "-C", str(staging), "remote", "add", "origin", pin["repository"]], check=True)
                subprocess.run(["git", "-C", str(staging), "fetch", "--quiet", "--depth=1", "origin", revision], check=True)
                subprocess.run(["git", "-C", str(staging), "-c", "advice.detachedHead=false",
                                "checkout", "--quiet", "--detach", revision], check=True)
                staging.rename(source)
        head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        changed = subprocess.check_output(["git", "-C", str(source), "status", "--porcelain",
                                           "--untracked-files=no"], text=True)
        if head != revision or changed:
            raise ValueError(f"formatter cache has unexpected source changes: {source}")
        environment = {**os.environ, "ELAN_TOOLCHAIN": toolchain}
        print(f"Formatter sources {revision[:12]}; compiler {toolchain}", flush=True)
        subprocess.run(["lake", "build", "lean-fmt"], cwd=source, env=environment, check=True)
    return source / ".lake/build/bin/lean-fmt", environment


def run_groups(root, groups, binary, environment, *, mode="check", workers=2):
    status = 0
    for package, files in groups.items():
        print(f"Syntax formatting: {package} ({len(files)} files)", flush=True)
        command = [str(binary), "format", "--root", str(root / package),
                   "--config", str(root / "lean-fmt.toml"), "--workers", str(workers)]
        if mode != "fix":
            command.append("--" + mode)
        command.extend(str(p) for p in files)
        result = subprocess.run(command, cwd=root / package, env=environment)
        status = max(status, result.returncode if result.returncode >= 0 else 2)
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true", help="read-only drift check (default)")
    modes.add_argument("--diff", action="store_true", help="read-only formatting patch")
    modes.add_argument("--fix", action="store_true", help="publish validated formatting")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--build-only", action="store_true", help="prepare the pinned formatter")
    parser.add_argument("--changed-from", metavar="REV",
                        help="only the package sources that differ from this revision")
    parser.add_argument("files", nargs="*", type=Path, help="repository-relative files; default: all package sources")
    args = parser.parse_args()
    try:
        if args.workers < 1:
            raise ValueError("workers must be positive")
        if args.changed_from and args.files:
            raise ValueError("--changed-from cannot be combined with files")
        pin = json.loads((ROOT / "tools/lean_format_tool.json").read_text())
        changed = changed_files(ROOT, args.changed_from) if args.changed_from else None
        groups, skipped = source_groups(ROOT, args.files, pin, changed)
        if changed is not None and not groups and not args.build_only:
            print(f"No Lean package source changed since {args.changed_from}.")
            return 0
        binary, environment = formatter()
        if args.build_only:
            return 0
        if skipped:
            print("Generated sources and standalone tooling scripts are excluded:",
                  ", ".join(map(str, skipped)), flush=True)
        mode = "fix" if args.fix else "diff" if args.diff else "check"
        return run_groups(ROOT, groups, binary, environment, mode=mode, workers=args.workers)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Lean formatting failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
