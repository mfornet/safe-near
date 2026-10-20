#!/usr/bin/env python3
"""Compare regular-key allowance restoration and native refund metadata."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
p = argparse.ArgumentParser()
p.add_argument("reference", type=Path)
p.add_argument("--report", type=Path, default=ROOT / "audit/allowance.json")
a = p.parse_args()
metadata = json.loads((ROOT / "audit/finance-reference-build.json").read_text())
assert metadata["sourceRevision"] == "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
assert metadata["sourceImplementationClean"]
assert hashlib.sha256(a.reference.read_bytes()).hexdigest() == metadata["binarySha256"]
assert hashlib.sha256((Path(__file__).parent / "adapter.rs").read_bytes()).hexdigest() == metadata["adapterSha256"]
lean = ROOT / "near-lean/runtime/.lake/build/bin/allowance-replay"

def run(binary, request):
    r = subprocess.run([str(binary)], input=json.dumps(request)+"\n", text=True,
                       capture_output=True, timeout=120)
    if r.returncode:
        raise RuntimeError(r.stderr)
    return json.loads(r.stdout)

maximum = 2**128 - 1
vectors = [("finite", amount, refunds, matching)
           for amount in [0, 1, maximum-1, maximum]
           for refunds in [[], [0], [1], [maximum], [1, 1, maximum]]
           for matching in [True, False]]
vectors += [(kind, 0, refunds, matching)
            for kind in ["full", "unlimited", "missing"]
            for refunds in [[0], [1], [maximum, 1]] for matching in [True, False]]
requests = [{"operation":"refundAllowance", "keyKind":kind, "allowance":str(allowance),
             "keyNonce":7, "targetMatches":matching, "receiverId":"contract.near", "methods":["go","callback"],
             "refunds":[str(v) for v in refunds]} for kind, allowance, refunds, matching in vectors]
for kind in ["finite", "unlimited"]:
    for receiver, methods in [("café.near", ["méthod"]), ("例.near", ["回调", "x"]),
                              ("alice.near", ["é", "😀"]), ("", [])]:
        requests.append({"operation":"refundAllowance", "keyKind":kind, "allowance":"3", "keyNonce":7,
                         "targetMatches":True, "receiverId":receiver, "methods":methods, "refunds":["2"]})
cases = []
for request in requests:
    reference = run(a.reference.resolve(), request)
    actual = run(lean, request)
    cases.append({"request":request,"reference":reference,"lean":actual,"passed":reference == actual})
failed = sum(not c["passed"] for c in cases)
a.report.parent.mkdir(parents=True, exist_ok=True)
a.report.write_text(json.dumps({"referenceBuild":metadata,"cases":cases,
                               "passed":len(cases)-failed,"failed":failed},indent=2)+"\n")
print(f"{len(cases)-failed} passed, {failed} differed; full evidence: {a.report}")
raise SystemExit(bool(failed))
