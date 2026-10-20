#!/usr/bin/env python3
"""Compare regenerated configuration tables, allowing only host VM selection.

nearcore selects its executable backend for the build architecture, and its own
config snapshots redact this field. The Lean parameter loader does not consume
vm_kind. Preserve both original views and check every other field and file.
"""
from __future__ import annotations

import argparse
import copy
import difflib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BACKENDS = {"Wasmer0", "Wasmer2", "NearVm", "Wasmtime"}


def normalized(value):
    value = copy.deepcopy(value)
    backend = value["wasm_config"].pop("vm_kind")
    if backend not in BACKENDS:
        raise ValueError(f"unknown native VM backend: {backend!r}")
    return value, backend


def compare(expected, actual):
    names = {p.name for p in expected.iterdir() if p.name != "README.md"}
    generated = {p.name for p in actual.iterdir() if p.name != "README.md"}
    if names != generated:
        raise ValueError(f"configuration file mismatch: missing={sorted(names - generated)}, extra={sorted(generated - names)}")
    backend_differences = []
    for name in sorted(names):
        if not name.startswith("runtime_config_v") or not name.endswith(".json"):
            raise ValueError(f"unexpected configuration file: {name}")
        left, left_backend = normalized(json.loads((expected / name).read_text()))
        right, right_backend = normalized(json.loads((actual / name).read_text()))
        before = json.dumps(left, indent=2, sort_keys=True).splitlines(True)
        after = json.dumps(right, indent=2, sort_keys=True).splitlines(True)
        if before != after:
            raise ValueError("".join(difflib.unified_diff(before, after, fromfile=f"committed/{name}", tofile=f"generated/{name}")))
        if left_backend != right_backend:
            backend_differences.append((name, left_backend, right_backend))
    return len(names), backend_differences


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("generated", type=Path)
    parser.add_argument("--expected", type=Path, default=ROOT / "near-lean/vm/configs")
    args = parser.parse_args()
    count, backends = compare(args.expected, args.generated)
    for name, left, right in backends:
        print(f"{name}: host VM selection {left} → {right}; all other fields match")
    print(f"Checked {count} configuration tables; {len(backends)} host backend differences.")


if __name__ == "__main__":
    main()
