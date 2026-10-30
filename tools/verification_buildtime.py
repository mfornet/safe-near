#!/usr/bin/env python3
"""Time a clean build of one contract's verification project, against a recorded baseline.

The project and every local package it requires by path are copied (tracked and
new files only, no build outputs) into a fresh directory that shares the
already-built external packages (mathlib and the rest). This is what a
developer focused on contract verification pays after a pull. The build fails
the gate when it is slower than the baseline for this machine by more than the
tolerance (notes/design/NEAR_NODE.md, M0).
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_toolchains import repository_files  # noqa: E402
from check_node_isolation import closure, packages  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / ".local/verification-buildtime.json"
SHARED_PACKAGES = Path("near-lean/.lake/packages")


def stage(root: Path, project: Path, destination: Path) -> None:
    """Copy `project` and its local package closure, sharing built external packages."""
    files = repository_files(root)
    local = closure(packages(root, files), project)
    for file in files:
        if file.name == "lean-toolchain" and file.parent == Path(".") or \
                any(file.is_relative_to(package) for package in local):
            if (root / file).is_file():
                (destination / file).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(root / file, destination / file)
    shared = root / SHARED_PACKAGES
    if not shared.is_dir():
        raise FileNotFoundError(f"{SHARED_PACKAGES} is missing; build near-lean once first")
    (destination / SHARED_PACKAGES).parent.mkdir(parents=True, exist_ok=True)
    os.symlink(shared, destination / SHARED_PACKAGES)


def timed_build(directory: Path, targets: list[str]) -> tuple[float, int]:
    started = time.monotonic()
    process = subprocess.run(["lake", "build", *targets], cwd=directory, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    seconds = time.monotonic() - started
    if process.returncode:
        print(process.stdout[-4000:], file=sys.stderr)
        raise RuntimeError(f"lake build failed in {directory}")
    jobs = re.search(r"Build completed successfully \((\d+) jobs?\)", process.stdout)
    return seconds, int(jobs[1]) if jobs else 0


def measure(root: Path, contract: str, targets: list[str], runs: int) -> dict:
    project = Path("contracts") / contract / "verification"
    samples, jobs = [], 0
    for _ in range(runs):
        with tempfile.TemporaryDirectory(prefix="safe-near-buildtime-") as directory:
            stage(root, project, Path(directory))
            seconds, jobs = timed_build(Path(directory) / project, targets)
            samples.append(round(seconds, 1))
    return {"seconds": min(samples), "samples": samples, "jobs": jobs, "targets": targets}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", default="w-near")
    parser.add_argument("--targets", nargs="*",
                        help="Lake targets to build (default: the baseline's, else the package defaults)")
    parser.add_argument("--runs", type=int, default=1, help="take the fastest of several clean builds")
    parser.add_argument("--tolerance", type=float, default=0.05)
    parser.add_argument("--record", action="store_true", help="store this machine's baseline instead of comparing")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args()
    baselines = json.loads(args.baseline.read_text()) if args.baseline.is_file() else {}
    key = args.contract
    targets = args.targets if args.targets is not None else baselines.get(key, {}).get("targets", [])
    try:
        result = measure(ROOT, args.contract, targets, args.runs)
    except (OSError, RuntimeError) as error:
        print(f"verification build-time check failed: {error}", file=sys.stderr)
        return 2
    print(f"{args.contract}: clean verification build {result['seconds']}s ({result['jobs']} jobs)")
    if args.record:
        result["recorded"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
        baselines[key] = result
        args.baseline.parent.mkdir(parents=True, exist_ok=True)
        args.baseline.write_text(json.dumps(baselines, indent=2, sort_keys=True) + "\n")
        print(f"Recorded baseline {key} in {args.baseline}")
        return 0
    if key not in baselines:
        print(f"No baseline for {key}; record one with --record", file=sys.stderr)
        return 2
    if baselines[key]["targets"] != targets:
        print(f"Targets {targets} differ from the baseline's {baselines[key]['targets']}", file=sys.stderr)
        return 2
    limit = baselines[key]["seconds"] * (1 + args.tolerance)
    if result["seconds"] > limit:
        print(f"Regression: {result['seconds']}s exceeds {limit:.1f}s "
              f"(baseline {baselines[key]['seconds']}s + {args.tolerance:.0%})", file=sys.stderr)
        return 1
    print(f"Within {args.tolerance:.0%} of baseline {baselines[key]['seconds']}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
