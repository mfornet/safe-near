#!/usr/bin/env python3
"""Check NearVM's import closure: the Wasm runtime, and no Talos interpreter, proof API or node packages."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def audit_source(report):
    return '''import NearVM
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let names := (← getEnv).header.moduleNames.map Name.toString
  let required := #["NearVM", "Wasm.Exec", "Wasm.Link", "Wasm.Validate"]
  let missing := required.filter (!names.contains ·)
  -- The legacy interpreter and proof API, and the node-side packages that
  -- contract verification must never build (notes/design/NEAR_NODE.md).
  let forbidden := names.filter fun name =>
    ["Interpreter", "CodeLib", "NearRuntime", "NearChain", "ChainReplay", "NearNode", "NodeBench"].any
      fun root => name == root || name.startsWith (root ++ ".")
  let relevant := names.filter fun name =>
    name == "NearVM" || name.startsWith "NearVM." || name.startsWith "Wasm."
  let report := Json.mkObj [
    ("modules", toJson relevant), ("missing", toJson missing),
    ("forbidden", toJson forbidden)]
  liftIO <| IO.FS.writeFile REPORT report.pretty
  unless missing.isEmpty do
    throwError "VM dependency audit is missing required execution modules: {missing}"
  unless forbidden.isEmpty do
    throwError "VM execution imports the legacy interpreter, proof API or node packages: {forbidden}"
'''.replace("REPORT", json.dumps(str(report.resolve()), ensure_ascii=False))


def audit(package, report):
    report = report.resolve()
    report.parent.mkdir(parents=True, exist_ok=True)
    report.unlink(missing_ok=True)
    with tempfile.TemporaryDirectory(prefix="safe-near-vm-deps-") as directory:
        source = Path(directory) / "CheckVMDependencies.lean"
        source.write_text(audit_source(report))
        return subprocess.run(["lake", "env", "lean", str(source)], cwd=package,
                              text=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/vm-dependencies.json")
    args = parser.parse_args()
    package = ROOT / "near-lean/vm"
    try:
        if not args.no_build:
            subprocess.run(["lake", "build", "NearVM"], cwd=package, check=True)
        process = audit(package, args.report)
        if process.returncode:
            print(process.stdout, end="", file=sys.stderr)
            print(process.stderr, end="", file=sys.stderr)
            return 1
        evidence = json.loads(args.report.read_text())
        if evidence["missing"] or evidence["forbidden"]:
            raise ValueError("dependency audit returned inconsistent evidence")
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"VM dependency audit failed: {error}", file=sys.stderr)
        return 2
    print(f"NearVM imports {len(evidence['modules'])} project modules; "
          "no legacy interpreter, proof API or node packages.")
    print(f"Full report: {args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
