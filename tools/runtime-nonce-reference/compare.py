#!/usr/bin/env python3
"""Exact comparison to nearcore's private nonce validator and version gate."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
p = argparse.ArgumentParser()
p.add_argument("reference", type=Path)
p.add_argument("--report", type=Path, default=ROOT / "audit/nonce.json")
a = p.parse_args()
metadata = json.loads((ROOT / "audit/nonce-reference-build.json").read_text())
assert metadata["sourceRevision"] == "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
assert metadata["sourceImplementationClean"]
assert hashlib.sha256(a.reference.read_bytes()).hexdigest() == metadata["binarySha256"]
assert hashlib.sha256((Path(__file__).parent / "adapter.rs").read_bytes()).hexdigest() == metadata["adapterSha256"]
lean = ROOT / "near-lean/runtime/.lake/build/bin/nonce-replay"

def run(binary, request):
    r = subprocess.run([str(binary)], input=json.dumps(request)+"\n", text=True,
                       capture_output=True, timeout=120)
    if r.returncode:
        raise RuntimeError(r.stderr)
    return json.loads(r.stdout)

maximum = 2**64 - 1
# Stale/equal/jumping nonces, exact ceiling, zero/unknown height, saturated
# multiplication and checked-add overflow. Every numeric input fits native u64.
vectors = [
    (0, 0, None), (1, 0, None), (2, 0, None), (9, 9, None), (8, 9, None),
    (10, 9, None), (11, 9, None), (1, 0, 0), (0, 0, 0),
    (999_999, 0, 1), (1_000_000, 0, 1), (1_000_001, 0, 1),
    (1_000_000, 999_999, 1), (1_000_000, 999_999, 2),
    (maximum, maximum-1, None), (maximum, maximum, None),
    (maximum-1, maximum-2, maximum), (maximum, maximum-1, maximum),
    (maximum, 0, maximum // 1_000_000 + 1),
    (maximum-1, 0, maximum // 1_000_000 + 1),
    (maximum, 0, maximum // 1_000_000),
]
cases = []
for version, mode, (nonce, current, height) in itertools.product([84, 85, 86], ["monotonic", "strict"], vectors):
    request = {"configDir":str(ROOT / "near-lean/vm/configs"), "protocolVersion":version,
               "nonceMode":mode, "nonce":nonce, "currentNonce":current, "blockHeight":height}
    reference = run(a.reference.resolve(), request)
    actual = run(lean, request)
    cases.append({"request":request, "reference":reference, "lean":actual, "passed":reference == actual})
failed = sum(not c["passed"] for c in cases)
a.report.parent.mkdir(parents=True, exist_ok=True)
a.report.write_text(json.dumps({"referenceBuild":metadata, "cases":cases,
                               "passed":len(cases)-failed, "failed":failed}, indent=2)+"\n")
print(f"{len(cases)-failed} passed, {failed} differed; full evidence: {a.report}")
raise SystemExit(bool(failed))
