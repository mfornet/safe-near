#!/usr/bin/env python3
"""Keep the NEAR node out of contract verification, and keep our Lean free of native code.

Three source-level rules from notes/design/NEAR_NODE.md, checked without
building anything:

1. No contract verification package reaches the node or chain packages through
   `[[require]] path = ...`, and no package other than the node itself requires
   the node. Contracts may require the runtime: their adapters run the binary
   through it.
2. No repository Lean source uses `@[extern]` or `@[implemented_by]`, and no
   lakefile links native code.
3. The node's protocol pin matches near-lean/runtime/reference.json.
4. The crypto package requires nothing from this repository, so NearVM can adopt it without
   pulling anything else in.
"""

import argparse
import json
import os
from pathlib import Path
import re
import sys
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_toolchains import repository_files  # noqa: E402

NODE = Path("near-lean/node")
CRYPTO = Path("near-lean/crypto")
# Packages the node builds on. Contract verification must not pay for them.
NODE_ONLY = {NODE, Path("near-lean/chain")}
NATIVE_ATTRIBUTE = re.compile(r"(@\[|attribute\s*\[)[^\]]*\b(extern|implemented_by)\b")
NATIVE_LAKE = re.compile(r"\b(extern_lib|moreLinkArgs|moreLeancArgs)\b")


def packages(root: Path, files: list[Path]) -> dict[Path, list[Path]]:
    """Map every repository package to the local packages it requires by path."""
    graph = {}
    for file in files:
        if file.name == "lakefile.toml" and (root / file).is_file():
            config = tomllib.loads((root / file).read_text())
            graph[file.parent] = [Path(os.path.normpath(file.parent / r["path"]))
                                  for r in config.get("require", []) if "path" in r]
    return graph


def closure(graph: dict[Path, list[Path]], start: Path) -> set[Path]:
    seen, todo = set(), [start]
    while todo:
        package = todo.pop()
        if package not in seen:
            seen.add(package)
            todo.extend(graph.get(package, []))
    return seen


def check_isolation(graph: dict[Path, list[Path]]) -> list[str]:
    errors = []
    for package in sorted(graph):
        if package.parts[:1] == ("contracts",):
            for reached in sorted(closure(graph, package) & NODE_ONLY):
                errors.append(f"{package}: contract verification depends on {reached}")
        if package != NODE and NODE in graph.get(package, []):
            errors.append(f"{package}: only the node may depend on {NODE}")
        if package == CRYPTO and graph[package]:
            errors.append(f"{package}: the crypto package must not require repository packages "
                          f"({', '.join(str(r) for r in sorted(graph[package]))})")
    return errors


def check_native(root: Path, files: list[Path]) -> list[str]:
    errors = []
    for file in files:
        path = root / file
        if not path.is_file():
            continue
        if file.suffix == ".lean":
            pattern, what = NATIVE_ATTRIBUTE, "native implementation attribute"
        elif file.name in {"lakefile.toml", "lakefile.lean"}:
            pattern, what = NATIVE_LAKE, "native link setting"
        else:
            continue
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if pattern.search(line):
                errors.append(f"{file}:{number}: {what}: {line.strip()}")
    return errors


def check_pin(root: Path) -> list[str]:
    source = root / NODE / "NearNode/Protocol.lean"
    if not source.is_file():
        return [f"{source.relative_to(root)}: missing"]
    text = source.read_text()
    reference = json.loads((root / "near-lean/runtime/reference.json").read_text())
    release = re.search(r'def nearcoreRelease : String := "([^"]*)"', text)
    version = re.search(r"def protocolVersion : Nat := (\d+)", text)
    errors = []
    if not release or release[1] != reference["release"]:
        errors.append(f"NearNode.Protocol: nearcoreRelease must be {reference['release']!r}")
    if not version or int(version[1]) != reference["reference_protocol_version"]:
        errors.append(f"NearNode.Protocol: protocolVersion must be {reference['reference_protocol_version']}")
    return errors


def check(root: Path) -> list[str]:
    files = repository_files(root)
    return check_isolation(packages(root, files)) + check_native(root, files) + check_pin(root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    errors = check(args.root)
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    print("Contract verification does not reach the node; the crypto package is self-contained; "
              "no native code in our Lean; protocol pin matches.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
