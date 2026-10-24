#!/usr/bin/env python3
"""Run the expensive validation suites locally, sequentially, with saved evidence."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import date, datetime, timezone
import fcntl
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "reports/periodic/LEDGER.json"

# Checklist sections of notes/design/PERIODIC_CHECK.md and the git pathspecs
# whose changes make each one due again. Pins and upgrades (None) follow
# upstream releases rather than our commits, so they are due by age instead.
PINS_MAX_AGE_DAYS = 7
# The check's own output must not make the next check due.
IGNORED = (":(exclude)reports/periodic",)
SECTIONS: dict[str, tuple[str, ...] | None] = {
    "build": ("near-lean", "contracts", "tools", "justfile"),
    "trusted-base": ("near-lean", ":(glob)contracts/*/verification/**"),
    "pins": None,
    "dead-code": ("near-lean", "contracts", "tools", "justfile", ".github"),
    "simplification": ("near-lean", ":(glob)contracts/*/verification/**"),
    "divergence": ("near-lean/vm", "near-lean/runtime", "near-lean/chain"),
    "docs": (".",),
    "tests-ci": ("near-lean", "tools", ".github", "justfile"),
    "features": (".",),
}


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
    python("nearcore-pin", "tools/check_nearcore_pin.py")
    add("tooling-tests", "", sys.executable, "-m", "unittest", "discover", "-s", "tools/tests", "-v")
    add("wasm-build", "near-lean/wasm", "lake", "build", "Wasm", "testsuite", "wasm", "--wfail")
    add("wasm-logic-build", "near-lean/wasm-logic", "lake", "build", "--wfail")
    add("interface-build", "near-lean/interface", "lake", "build", "NearInterface", "--wfail")
    add("vm-build", "near-lean/vm", "lake", "build", "NearVM", "vm-tests", "vm-replay", "--wfail")
    add("runtime-build", "near-lean/runtime", "lake", "build", "NearRuntime", "runtime-tests",
        "NearRuntime.TrieAccounting", "finance-replay", "nonce-replay", "allowance-replay",
        "staking-key-replay", "trie-replay", "--wfail")
    add("chain-build", "near-lean/chain", "lake", "build", "NearChain", "chain-tests", "chain-replay",
        "registered-replay", "state-encode", "receipt-encode", "transaction-replay", "receipt-replay", "--wfail")
    # Contracts with a ContractModel instance: the adapter executable compares the
    # binary with the model; `refines_<name>` in Proofs.Refinement is the open proof.
    adapter_contracts = [("w-near", "wnear")]
    for contract, report in adapter_contracts:
        add(f"{report}-adapter-build", f"contracts/{contract}/verification", "lake", "build", "Spec",
            "runtime-adapter-tests", "--wfail")
        add(f"{report}-proofs-build", f"contracts/{contract}/verification", "lake", "build", "Model", "Proofs")
    # New contract projects join the sequential build/audit gate automatically.
    contract_projects = sorted({manifest.parent for pattern in ("*/verification/lakefile.toml",
                                                               "*/verification/lakefile.lean")
                                for manifest in (root / "contracts").glob(pattern)
                                if manifest.parent.parent.name not in dict(adapter_contracts)})
    for project in contract_projects:
        name = project.parent.name
        add(f"contract-{name}-build", project.relative_to(root), "lake", "build", "--wfail")
    for package, binary in [("vm", "vm-tests"), ("runtime", "runtime-tests"), ("chain", "chain-tests")]:
        add(binary, f"near-lean/{package}", f"./.lake/build/bin/{binary}")
    for contract, report in adapter_contracts:
        add(f"{report}-adapter-tests", f"contracts/{contract}/verification", "./.lake/build/bin/runtime-adapter-tests")
    python("chain-json-replay", "tools/chain-conformance/test_replay.py")
    add("wasm-validate-smoke", "near-lean/wasm", "./.lake/build/bin/wasm", "validate",
        "../../contracts/w-near/contract.wasm")
    add("wasm-spec-report", "", "near-lean/wasm/scripts/testsuite-report.sh")
    add("wasm-spec-report-clean", "", "git", "diff", "--exit-code", "--", "near-lean/wasm/testsuite_report.txt")
    # The separation logic's examples: committed binaries match their .wat,
    # the linked client runs as proved, and every mutant of the proved code
    # breaks a proof.
    add("wasm-logic-bytes", "near-lean/wasm-logic", "scripts/check-wasm-bytes.sh")
    add("wasm-logic-smoke", "near-lean/wasm-logic", "scripts/smoke-client.sh")
    add("wasm-logic-mutants", "near-lean/wasm-logic", sys.executable, "scripts/mutation-test.py")
    python("lean-style", "tools/lean_style.py")
    python("style-regressions", "tools/tests/check_lean_style.py")
    python("formatter-regressions", "tools/tests/check_lean_format.py")
    python("vm-dependencies", "tools/check_vm_dependencies.py", "--no-build")
    python("dependency-regressions", "tools/tests/check_vm_dependencies.py")
    python("audit-regressions", "tools/tests/check_axiom_audit.py")
    for package, report in [("near-lean/wasm", "wasm"), ("near-lean/wasm-logic", "wasm-logic"),
                            ("near-lean/interface", "interface"), ("near-lean/vm", "vm"),
                            ("near-lean/runtime", "runtime"), ("near-lean/chain", "chain")]:
        python(f"audit-{report}", "tools/axiom-audit.py", package, "--no-build", "--report", f"audit/{report}.json")
    for contract, report in adapter_contracts:
        python(f"audit-{report}", "tools/axiom-audit.py", f"contracts/{contract}/verification", "--no-build",
               "--allow-sorry-module", "Proofs.Refinement", "--report", f"audit/{report}.json")
    for project in contract_projects:
        name = project.parent.name
        python(f"audit-contract-{name}", "tools/axiom-audit.py", project.relative_to(root),
               "--no-build", "--report", f"audit/{name}.json")
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
    python("receipt-reference-build", "tools/runtime-receipt-reference/build.py", nearcore)
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
    python("receipt-result-conformance", "tools/runtime-receipt-reference/compare.py",
           nearcore / "target/debug/safe-near-receipt-reference", "--scope", "receipt-results")
    python("chain-reference-smoke", "tools/chain-conformance/probe.py")
    python("chain-gas", "tools/chain-conformance/gas_probe.py")
    for name in ["snapshot_import", "contract_comparison", "chunk_storage_accounting", "transaction_versions", "action_comparison",
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


def read_ledger(path: Path) -> dict:
    return json.loads(path.read_text())["sections"] if path.exists() else {}


def due_sections(root: Path, ledger: dict, today: date | None = None) -> list[tuple[str, str]]:
    """Sections to run, each with the reason it is due."""
    today = today or datetime.now(timezone.utc).date()
    due = []
    for name, paths in SECTIONS.items():
        entry = ledger.get(name, {})
        commit = entry.get("commit")
        if not commit:
            due.append((name, "never checked"))
            continue
        if paths is None:
            age = (today - date.fromisoformat(entry["date"])).days
            if age >= PINS_MAX_AGE_DAYS:
                due.append((name, f"last checked {age} days ago"))
            continue
        diff = subprocess.run(["git", "diff", "--name-only", commit, "HEAD", "--", *paths, *IGNORED],
                              cwd=root, text=True, capture_output=True)
        if diff.returncode:
            due.append((name, f"last checked commit {commit[:7]} is not in this repository"))
        elif changed := diff.stdout.splitlines():
            due.append((name, f"{len(changed)} files changed since {commit[:7]}"))
    return due


def record_sections(root: Path, path: Path, sections: list[str], report: str, issues: list[str]) -> None:
    """Mark sections as checked at HEAD by the given report."""
    if unknown := set(sections) - SECTIONS.keys():
        raise ValueError(f"unknown sections: {', '.join(sorted(unknown))}")
    ledger = read_ledger(path)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    today = datetime.now(timezone.utc).date().isoformat()
    for name in sections:
        ledger[name] = {"commit": commit, "date": today, "report": report, "issues": issues}
    ordered = {name: ledger[name] for name in SECTIONS if name in ledger}
    path.write_text(json.dumps({"sections": ordered}, indent=2) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nearcore", type=Path, help="clean checkout at the finance/nonce source pin")
    parser.add_argument("--plan", action="store_true", help="print the complete command plan without running it")
    parser.add_argument("--output", type=Path, help="new evidence directory (default: audit/periodic/<UTC timestamp>)")
    parser.add_argument("--due", action="store_true", help="list the checklist sections with changes since their last check")
    parser.add_argument("--record", nargs="+", metavar="SECTION", help="mark sections as checked at HEAD")
    parser.add_argument("--report", help="with --record: the report that covers the sections")
    parser.add_argument("--issue", action="append", default=[], help="with --record: a Linear issue the check filed")
    parser.add_argument("--ledger", type=Path, default=LEDGER, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.due:
        due = due_sections(ROOT, read_ledger(args.ledger))
        for name, reason in due:
            print(f"{name}: {reason}")
        if not due:
            print("Nothing is due.")
        return 0
    if args.record:
        if not args.report:
            parser.error("--record needs --report")
        try:
            record_sections(ROOT, args.ledger, args.record, args.report, args.issue)
        except ValueError as error:
            parser.error(str(error))
        return 0
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
