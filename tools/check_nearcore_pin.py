#!/usr/bin/env python3
"""Require every hardcoded nearcore revision to match near-lean/runtime/reference.json."""

import argparse
import json
from pathlib import Path
import re
import sys

from check_lean_toolchains import repository_files

REFERENCE = Path("near-lean/runtime/reference.json")
SHA = re.compile(r"\b[0-9a-f]{40}\b")
URL = re.compile(r"near/nearcore/(?:blob|tree|commit)/([0-9a-f]{40})")
CHECKOUT = re.compile(r"repository:\s*near/nearcore\s*$")
REF = re.compile(r"^\s*ref:\s*([0-9a-f]{40})\s*$")
# The native reference adapters, whose scripts and READMEs name only nearcore.
ADAPTER = re.compile(r"tools/runtime-[a-z]+-reference/")


def pins(path: Path, text: str) -> list[tuple[int, str]]:
    """The nearcore revisions written in one file, with their line numbers."""
    found = []
    lines = text.splitlines()
    for number, line in enumerate(lines, 1):
        if ADAPTER.match(path.as_posix()):
            found += [(number, sha) for sha in SHA.findall(line)]
        else:
            found += [(number, sha) for sha in URL.findall(line)]
        if path.parts[:2] == (".github", "workflows") and CHECKOUT.search(line):
            # The checkout's `ref:` follows within the same `with:` block.
            for offset, after in enumerate(lines[number:number + 4], number + 1):
                if match := REF.match(after):
                    found.append((offset, match.group(1)))
                    break
    return found


def check(root: Path) -> list[str]:
    reference = root / REFERENCE
    if not reference.is_file():
        return [f"missing {REFERENCE}"]
    expected = json.loads(reference.read_text())["revision"]
    errors = []
    for path in repository_files(root):
        if path == REFERENCE or path.parts[0] == "reports" or not (root / path).is_file():
            continue
        try:
            text = (root / path).read_text()
        except UnicodeDecodeError:
            continue
        for number, sha in pins(path, text):
            if sha != expected:
                errors.append(f"{path}:{number}: nearcore revision {sha}, expected {expected}")
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
    print(f"Every hardcoded nearcore revision matches {REFERENCE}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
