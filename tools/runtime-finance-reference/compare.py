#!/usr/bin/env python3
"""Compare tx cost and refund settlement to pinned runtime entry points."""
import argparse
import itertools
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
p = argparse.ArgumentParser()
p.add_argument("reference", type=Path)
p.add_argument("--report", type=Path, default=ROOT / "audit/finance.json")
a = p.parse_args()
lean = ROOT / "near-lean/runtime/.lake/build/bin/finance-replay"
metadata = json.loads((ROOT / "audit/finance-reference-build.json").read_text())
assert metadata["sourceRevision"] == "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
assert metadata["sourceImplementationClean"]
assert hashlib.sha256(a.reference.read_bytes()).hexdigest() == metadata["binarySha256"]
assert hashlib.sha256((Path(__file__).parent / "adapter.rs").read_bytes()).hexdigest() == metadata["adapterSha256"]

def run(binary, request):
    r = subprocess.run([str(binary)], input=json.dumps(request) + "\n", text=True,
                       capture_output=True, timeout=120)
    if r.returncode:
        raise RuntimeError(r.stderr)
    return json.loads(r.stdout)

cases = []
# Gas figures include the create-account execution cost, where applicable;
# this is the financial seam, not an execution oracle for these action lists.
for version, purchase, current, created in itertools.product(
        [84, 85, 86], [100_000_000, 1_000_000_000, 2_000_000_000],
        [0, 100_000_000, 1_000_000_000, 3_000_000_000], [False, True]):
    request = {"configDir":str(ROOT / "near-lean/vm/configs"), "protocolVersion":version,
               "currentPrice":str(current), "purchasePrice":str(purchase),
               "prepaidGas":100_000_000_000_000, "burntGas":20_000_000_000_000,
               "usedGas":30_000_000_000_000, "createdAccount":created}
    reference = run(a.reference.resolve(), request)
    actual = run(lean, request)
    cases.append({"request":request, "reference":reference, "lean":actual,
                  "passed":reference == actual})
failed = sum(not c["passed"] for c in cases)
a.report.parent.mkdir(parents=True, exist_ok=True)
a.report.write_text(json.dumps({"sourceRevision":"44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
                                "referenceBuild":metadata, "cases":cases, "passed":len(cases)-failed, "failed":failed}, indent=2)+"\n")
print(f"{len(cases)-failed} passed, {failed} differed; full evidence: {a.report}")
raise SystemExit(bool(failed))
