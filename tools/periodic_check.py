#!/usr/bin/env python3
"""Run the expensive validation suites locally, sequentially, with saved evidence."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Step:
    name: str
    directory: Path
    command: tuple[str, ...]


def validation_steps(root: Path, nearcore: Path) -> list[Step]:
    steps = []

    def add(name, directory, *command):
        steps.append(Step(name, root / directory, tuple(str(arg) for arg in command)))

    def python(name, script, *args):
        add(name, "", sys.executable, script, *args)

    # Build each package sequentially. Finish every executor build before native
    # comparisons freeze and attest their binaries.
    python("toolchains", "tools/check_lean_toolchains.py")
    add("tooling-tests", "", sys.executable, "-m", "unittest", "discover", "-s", "tools/tests", "-v")
    add("wasm-build", "near-lean/wasm", "lake", "build", "Interpreter", "runner", "testsuite")
    add("iris-build", "near-lean/iris-wasm", "lake", "build", "--wfail")
    add("programs-build", "near-lean/programs/lean", "lake", "build", "Programs", "smoke", "program-tests", "--wfail")
    add("vm-build", "near-lean/vm", "lake", "build", "NearVM", "vm-tests", "vm-replay", "--wfail")
    add("runtime-build", "near-lean/runtime", "lake", "build", "NearRuntime", "runtime-tests",
        "finance-replay", "nonce-replay", "allowance-replay", "staking-key-replay", "trie-replay", "--wfail")
    add("chain-build", "near-lean/chain", "lake", "build", "NearChain", "chain-tests", "chain-replay",
        "registered-replay", "state-encode", "receipt-encode", "transaction-replay", "--wfail")
    add("wnear-adapter-build", "contracts/w-near/verification", "lake", "build", "Spec", "runtime-adapter-tests", "--wfail")
    add("wnear-proofs-build", "contracts/w-near/verification", "lake", "build", "Model", "Proofs")
    for package, binary in [("vm", "vm-tests"), ("runtime", "runtime-tests"), ("chain", "chain-tests"),
                            ("programs/lean", "smoke"), ("programs/lean", "program-tests")]:
        add(binary, f"near-lean/{package}", f"./.lake/build/bin/{binary}")
    add("wnear-adapter-tests", "contracts/w-near/verification", "./.lake/build/bin/runtime-adapter-tests")
    python("chain-json-replay", "tools/chain-conformance/test_replay.py")
    add("wasm-runner-smoke", "", "near-lean/wasm/scripts/runner-smoke.sh")
    add("wasm-spec-report", "", "near-lean/wasm/scripts/testsuite-report.sh")
    add("wasm-spec-report-clean", "", "git", "diff", "--exit-code", "--", "near-lean/wasm/testsuite_report.txt")
    python("lean-style", "tools/lean_style.py")
    python("style-regressions", "tools/tests/check_lean_style.py")
    python("syntax-format", "tools/lean_format.py", "--check",
           "near-lean/programs/lean/Programs/Harness.lean", "near-lean/programs/lean/Programs/Regression.lean")
    python("formatter-regressions", "tools/tests/check_lean_format.py")
    python("vm-dependencies", "tools/check_vm_dependencies.py", "--no-build")
    python("dependency-regressions", "tools/tests/check_vm_dependencies.py")
    python("audit-regressions", "tools/tests/check_axiom_audit.py")
    for package, report in [("near-lean/wasm", "wasm"), ("near-lean/iris-wasm", "iris-wasm"),
                            ("near-lean/programs/lean", "programs"), ("near-lean/vm", "vm"),
                            ("near-lean/runtime", "runtime"), ("near-lean/chain", "chain"),
                            ("contracts/w-near/verification", "wnear")]:
        python(f"audit-{report}", "tools/axiom-audit.py", package, "--no-build", "--report", f"audit/{report}.json")
    add("program-wasm-rebuild", "", "near-lean/programs/rust/build.sh")
    add("program-wasm-clean", "", "git", "diff", "--exit-code", "--", "near-lean/programs/rust/build")
    add("program-rust-tests", "near-lean/programs/rust", "cargo", "test", "--locked")
    generated = root / "audit/periodic-runtime-configs"
    add("runtime-config-generation", "", "cargo", "run", "--locked", "--release", "--manifest-path",
        "tools/dump-runtime-config/Cargo.toml", "--", generated)
    python("runtime-config-comparison", "tools/check_runtime_configs.py", generated)
    for name, fixture in [("replay", "tools/chain-conformance/fixtures/replay"),
                          ("stateful", "tools/chain-conformance/fixtures/stateful"),
                          ("storage-inputs", "tools/runtime-conformance/fixtures/storage_inputs")]:
        output = root / f"audit/periodic-{name}.wasm"
        add(f"fixture-{name}", "", "wasm-tools", "parse", f"{fixture}.wat", "-o", output)
        add(f"fixture-{name}-clean", "", "cmp", f"{fixture}.wasm", output)
    add("vm-reference-build", "tools/runtime-conformance", "cargo", "build", "--locked", "--quiet")
    python("finance-reference-build", "tools/runtime-finance-reference/build.py", nearcore)
    python("nonce-reference-build", "tools/runtime-nonce-reference/build.py", nearcore)
    # prepare.py uses its own clean source cache; the finance/nonce checkout is
    # intentionally separate from the Runtime::apply reference's custody.
    python("chain-reference-build", "tools/chain-conformance/prepare.py")
    add("vm-comparison-tests", "", sys.executable, "-m", "unittest", "discover", "-s",
        "tools/runtime-conformance", "-p", "test_*.py", "-v")
    python("vm-conformance", "tools/runtime-conformance/compare.py", "--no-build")
    finance = nearcore / "target/debug/safe-near-finance-reference"
    python("finance-conformance", "tools/runtime-finance-reference/compare.py", finance)
    python("allowance-conformance", "tools/runtime-finance-reference/compare_allowance.py", finance)
    python("nonce-conformance", "tools/runtime-nonce-reference/compare.py",
           nearcore / "target/debug/safe-near-nonce-reference")
    python("chain-reference-smoke", "tools/chain-conformance/probe.py")
    python("chain-gas", "tools/chain-conformance/gas_probe.py")
    for name in ["snapshot_import", "contract_comparison", "transaction_versions", "action_comparison",
                 "permission_comparison", "action_validation", "transaction_size", "staking_key",
                 "trie_accounting", "trie_updates", "state_encoding", "receipt_encoding", "queue_encoding",
                 "transaction_encoding", "delayed_local_order", "receipt_registry", "registered_comparison",
                 "action_randomness"]:
        python(f"chain-{name}", f"tools/chain-conformance/test_{name}.py")
    return steps


def run_steps(steps: list[Step], output: Path, revision: str, dirty: bool = False) -> int:
    if not steps:
        raise ValueError("an empty validation plan cannot pass")
    output.mkdir(parents=True, exist_ok=False)
    report = {"revision": revision, "workingTreeDirty": dirty, "started": datetime.now(timezone.utc).isoformat(),
              "status": "running", "steps": []}
    summary = output / "summary.json"
    for index, step in enumerate(steps, 1):
        print(f"[{index}/{len(steps)}] {step.name}", flush=True)
        started = time.monotonic()
        log = output / f"{index:02d}-{step.name}.log"
        with log.open("w") as stream:
            try:
                code = subprocess.run(step.command, cwd=step.directory, stdout=stream,
                                      stderr=subprocess.STDOUT).returncode
            except OSError as error:
                stream.write(str(error) + "\n")
                code = 127
        report["steps"].append({"name": step.name, "directory": str(step.directory),
                                "command": list(step.command), "exitCode": code,
                                "seconds": round(time.monotonic() - started, 3), "log": str(log)})
        report["status"] = "failed" if code else ("passed" if index == len(steps) else "running")
        summary.write_text(json.dumps(report, indent=2) + "\n")
        if code:
            print(f"Failed: {step.name}. See {log}", file=sys.stderr)
            return code if code > 0 else 1
    print(f"All {len(steps)} checks passed. Evidence: {summary}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nearcore", type=Path, help="clean checkout at the finance/nonce source pin")
    parser.add_argument("--plan", action="store_true", help="print the complete command plan without running it")
    parser.add_argument("--output", type=Path, help="new evidence directory (default: audit/periodic/<UTC timestamp>)")
    args = parser.parse_args()
    nearcore = (args.nearcore or ROOT / "reference-nearcore").resolve()
    steps = validation_steps(ROOT, nearcore)
    if args.plan:
        for step in steps:
            print(f"{step.name}: (cd {shlex.quote(str(step.directory))} && {shlex.join(step.command)})")
        return 0
    if args.nearcore is None or not (nearcore / ".git").exists():
        parser.error("--nearcore must name a clean pinned nearcore checkout; use --plan to preview")
    pin = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())["revision"]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=nearcore, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=nearcore, text=True)
    if revision != pin or dirty:
        parser.error(f"nearcore must be clean and checked out at {pin}")
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = (args.output or ROOT / "audit/periodic" / timestamp).resolve()
    lock_path = ROOT / "audit/periodic.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            parser.error("another periodic check is running in this checkout")
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
        return run_steps(steps, output, revision, dirty)


if __name__ == "__main__":
    raise SystemExit(main())
