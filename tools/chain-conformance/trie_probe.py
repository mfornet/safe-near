#!/usr/bin/env python3
"""Compare canonical trie construction, object bytes, lookups and cache accounting.

This is a trie diagnostic, not receipt gas injection or full runtime equivalence.
Lean constructs the canonical trie from raw entries using pure SHA256; no native
root, witness, path or count is supplied to its constructor. Complete object
bytes, roots, paths, dereferences and fresh/cached counts are compared exactly.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from gas_probe import differences
from import_snapshot import execute, native_call
from prepare import HERE, ROOT, atomic_write
from probe import file_digest, frozen_reference

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/runtime/.lake/build/bin/trie-replay"
MODE = "canonical-on-disk/no-flat-storage/no-memtrie"


@contextmanager
def frozen_model(binary):
    checksum = file_digest(binary)
    with tempfile.TemporaryDirectory(prefix="safe-near-trie-model-") as temporary:
        frozen = Path(temporary) / "trie-replay"
        shutil.copy2(binary, frozen)
        if file_digest(frozen) != checksum:
            raise ValueError("trie model changed while being frozen")
        yield frozen, checksum
        if file_digest(frozen) != checksum:
            raise ValueError("frozen trie model changed during comparison")


def checked_model_request(request, native):
    if native["formatVersion"] != 1 or native["mode"] != MODE:
        raise ValueError("unsupported native trie witness mode")
    root = native["root"]
    if len(root) != 32 or any(type(byte) is not int or not 0 <= byte < 256 for byte in root):
        raise ValueError("invalid trie root")
    hashes = set()
    for identifier, payload in native["witness"]:
        for data in [identifier, payload]:
            if any(type(byte) is not int or not 0 <= byte < 256 for byte in data):
                raise ValueError("invalid witness byte")
        identifier = bytes(identifier)
        if identifier in hashes or len(identifier) != 32:
            raise ValueError("duplicate or invalid witness hash")
        hashes.add(identifier)
        if hashlib.sha256(bytes(payload)).digest() != identifier:
            raise ValueError("trie witness hash does not bind its bytes")
    return dict(formatVersion=1, root=root, witness=native["witness"], lookups=request["lookups"])


def compare(request, native, model):
    expected = native_call(native, "--trie-lookups", request)
    checked_model_request(request, expected)
    if expected.get("witnessComplete") is not True:
        raise ValueError("native trie witness is incomplete")
    try:
        actual = execute(model, request, ROOT)
    except subprocess.CalledProcessError as error:
        message = error.stderr.strip()
        return dict(request=request, native=expected, model=None, modelExecutionError=message,
            differences=[dict(path="execution", error=message)])
    def projection(value, native=False):
        for identifier, payload in value["witness"]:
            if len(identifier) != 32 or any(type(byte) is not int or not 0 <= byte < 256
                    for data in [identifier, payload] for byte in data):
                raise ValueError("invalid trie witness object")
        witness = {bytes(identifier).hex(): payload for identifier, payload in value["witness"]}
        if len(witness) != len(value["witness"]):
            raise ValueError("duplicate trie witness object")
        result = {**value, "witness": witness}
        if native:
            for key in ["formatVersion", "mode", "witnessComplete"]:
                del result[key]
        return result
    try:
        diffs = differences(projection(expected, native=True), projection(actual))
    except (ValueError, KeyError, TypeError) as error:
        diffs = [dict(path="projection", error=str(error))]
    return dict(request=request, native=expected, model=actual, modelExecutionError=None, differences=diffs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", type=Path)
    parser.add_argument("--reference", type=Path, default=REFERENCE)
    parser.add_argument("--model", type=Path, default=MODEL)
    parser.add_argument("--report", type=Path, default=ROOT / "audit/trie-lookup-comparison.json")
    arguments = parser.parse_args()
    request = json.loads(arguments.request.read_text())
    with frozen_reference(arguments.reference) as (native, build), frozen_model(arguments.model) as (model, checksum):
        report = compare(request, native, model)
    report.update(referenceBuild=build, modelBinarySha256=checksum, runtimeIntegrated=False,
        witnessHashBinding="pure Lean SHA256, independently checked externally",
        nodeTraversal="Lean canonical construction from raw entries, Borsh decoding and cache")
    atomic_write(arguments.report.resolve(), (json.dumps(report, indent=2) + "\n").encode())
    print(f"{len(report['native']['results'])} lookups; {len(report['differences'])} differences; {arguments.report}")
    raise SystemExit(bool(report["differences"]))


if __name__ == "__main__":
    main()
