#!/usr/bin/env python3
"""Run identical VM requests through pinned nearcore and Lean; fail on any diff.

The report retains complete requests and outputs, including gas discrepancies.
Reference storage feeds each subsequent case so both executors always receive
identical input. This is a VM oracle, not a transaction/receipt runtime oracle.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
TOOL = Path(__file__).resolve().parent


def differences(expected, actual, path="$"):
    if type(expected) is not type(actual):
        return [{"path": path, "reference": expected, "lean": actual}]
    if isinstance(expected, dict):
        result = []
        for key in sorted(expected.keys() | actual.keys()):
            if key not in expected or key not in actual:
                result.append({"path": f"{path}.{key}", "reference": expected.get(key), "lean": actual.get(key)})
            else:
                result.extend(differences(expected[key], actual[key], f"{path}.{key}"))
        return result
    if isinstance(expected, list):
        if len(expected) != len(actual):
            return [{"path": path, "reference": expected, "lean": actual}]
        return [diff for index, (a, b) in enumerate(zip(expected, actual))
                for diff in differences(a, b, f"{path}[{index}]")]
    return [] if expected == actual else [{"path": path, "reference": expected, "lean": actual}]


def run_json(binary, request):
    process = subprocess.run([str(binary)], input=json.dumps(request) + "\n",
                             text=True, capture_output=True, timeout=120)
    if process.returncode:
        raise RuntimeError(f"{binary.name} exited {process.returncode}: {process.stderr.strip()}")
    return json.loads(process.stdout)


def compare_fixture(fixture_path, version):
    fixture = json.loads(fixture_path.read_text())
    code = ROOT / fixture["code"]
    digest = hashlib.sha256(code.read_bytes()).hexdigest()
    if digest != fixture["sha256"]:
        raise ValueError("fixture binary does not match its pinned SHA256")
    reference = TOOL / "target/debug/near-runtime-reference"
    lean = ROOT / "near-lean/vm/.lake/build/bin/vm-replay"
    report = {"reference": json.loads((ROOT / "near-lean/runtime/reference.json").read_text()),
              "fixture": str(fixture_path.resolve()), "codeSha256": digest,
              "wasmTools": version, "cases": [], "notRun": []}
    with tempfile.TemporaryDirectory(prefix="safe-near-conformance-") as temp:
        wat = Path(temp) / "contract.wat"
        subprocess.run(["wasm-tools", "print", str(code), "-o", str(wat)], check=True)
        state = {"storage": fixture["storage"], "balance": fixture["initialBalance"],
                 "storageUsage": fixture.get("initialStorageUsage", code.stat().st_size + 182)}
        for case_index, case in enumerate(fixture["calls"]):
            predecessor = case.get("predecessor", "alice.near")
            request = {
                "codePath": str(code), "watPath": str(wat),
                "validateActionMethodUtf8": case.get("validateActionMethodUtf8", fixture.get("validateActionMethodUtf8", False)),
                "configDir": str(ROOT / "near-lean/vm/configs"),
                "protocolVersion": fixture["protocolVersion"], "method": case["method"],
                "currentAccountId": "wrap.near", "signerAccountId": case.get("signer", predecessor),
                "signerAccountPk": [0] + [1] * 32, "predecessorAccountId": predecessor,
                "input": list(json.dumps(case["args"], separators=(",", ":"), ensure_ascii=False).encode()),
                "promiseResults": case.get("promiseResults", []),
                "blockHeight": 1, "blockTimestamp": 0, "epochHeight": 0,
                "accountBalance": state["balance"], "accountLockedBalance": "0",
                "storageUsage": state["storageUsage"], "attachedDeposit": case.get("deposit", "0"),
                "prepaidGas": case.get("gas", 100_000_000_000_000), "randomSeed": [0] * 32,
                "view": case.get("view", False),
                "outputDataReceivers": case.get("outputDataReceivers", []), "storage": state["storage"],
                "validators": case.get("validators", fixture.get("validators", []))}
            try:
                expected = run_json(reference, request)
                actual = run_json(lean, request)
            except (RuntimeError, subprocess.TimeoutExpired, json.JSONDecodeError) as error:
                report["cases"].append({"name": case["name"], "request": request,
                    "executionError": str(error), "differences": [{"path": "$.execution", "error": str(error)}]})
                report["notRun"] = [remaining["name"] for remaining in fixture["calls"][case_index + 1:]]
                print(f"FAIL: {case['name']} ({error})", flush=True)
                break
            diffs = differences(expected, actual)
            report["cases"].append({"name": case["name"], "request": request,
                                    "reference": expected, "lean": actual, "differences": diffs})
            print(f"{'FAIL' if diffs else 'PASS'}: {case['name']}" +
                  (" (" + ", ".join(d["path"] for d in diffs[:8]) + ")" if diffs else ""), flush=True)
            state = expected
        # Retain the generated decoder input after the temporary directory goes away.
        report["wat"] = wat.read_text()
    report["passed"] = sum(not case["differences"] for case in report["cases"])
    report["failed"] = len(report["cases"]) - report["passed"] + len(report["notRun"])
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, action="append", help="Repeat to select fixtures; defaults to all")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/runtime-conformance.json")
    parser.add_argument("--no-build", action="store_true")
    args = parser.parse_args()
    if not args.no_build:
        subprocess.run(["cargo", "build", "--locked", "--quiet"], cwd=TOOL, check=True)
        subprocess.run(["lake", "build", "vm-replay", "--wfail"], cwd=ROOT / "near-lean/vm", check=True)
    version = subprocess.check_output(["wasm-tools", "--version"], text=True).strip()
    if version != "wasm-tools 1.251.0":
        raise ValueError(f"expected wasm-tools 1.251.0, found {version}")
    fixtures = args.fixture or sorted((TOOL / "fixtures").glob("*.json"))
    if not fixtures:
        raise ValueError("no conformance fixtures selected")
    results = [compare_fixture(fixture, version) for fixture in fixtures]
    report = {"fixtures": results, "passed": sum(r["passed"] for r in results),
              "failed": sum(r["failed"] for r in results)}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"{report['passed']} passed, {report['failed']} differed; full evidence: {args.report}")
    return int(report["failed"] != 0)


if __name__ == "__main__":
    raise SystemExit(main())
