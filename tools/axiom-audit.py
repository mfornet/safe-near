#!/usr/bin/env python3
"""Audit every source module in a Lake package for nonstandard axioms.

The gate for a finished proof: every declaration may depend only on the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). In particular
no `sorryAx` (an open proof) and no `Lean.ofReduceBool` (`native_decide`,
which trusts the compiler rather than the kernel).

Usage:
  tools/axiom-audit.py near-lean/wasm --report audit/wasm.json
  tools/axiom-audit.py near-lean/programs/lean --report audit/programs.json

Unlike an umbrella import or a source grep, this checks the transitive axiom
dependencies of every declaration, including private helpers and proof fields
in definitions. Untracked, nonignored Lean sources are included. Nested Lake
packages must be audited separately. A missing module or failed build is an
audit failure, never an exemption.

`--allow-sorry` tolerates `sorryAx` alone, for packages whose proofs are
intentionally left open in an unfinished proof package; the sorried
declarations are listed, and every other nonstandard axiom still fails.
Repeat --require-clean-module to keep completed modules strict within such a
package; a missing required module is an audit error.
Use --allow-sorry-module instead of --allow-sorry to limit open proofs to named
modules while keeping every other module strict.

Adapted from Talos `scripts/axiom-audit.py` (the verifier-template audit was
dropped; near-lean has no verifier).
"""

import argparse
from collections.abc import Sequence
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def source_modules(root: Path, package: Path) -> list[str]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others",
         "--exclude-standard", "--", "*.lean"],
        check=True, stdout=subprocess.PIPE,
    )
    modules = set()
    for filename in result.stdout.decode().split("\0"):
        if not filename:
            continue
        path = root / filename
        # `--cached` also lists files deleted in the working tree but not yet
        # staged; the audit covers what is actually on disk.
        if not path.is_file() or not path.is_relative_to(package):
            continue
        parents = path.relative_to(package).parents
        if any(
            parent != Path(".") and any(
                (package / parent / manifest).exists()
                for manifest in ("lakefile.toml", "lakefile.lean")
            )
            for parent in parents
        ):
            continue
        modules.add(".".join(path.relative_to(package).with_suffix("").parts))
    return sorted(modules)


def audit_source(modules: list[str], report: Path) -> str:
    imports = "\n".join(f"import {module}" for module in modules)
    expected = ", ".join(json.dumps(module) for module in modules)
    standard = " && ".join(f"a != `{axiom}" for axiom in STANDARD_AXIOMS)
    return imports + f"""
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected : Array String := #[{expected}]
  for moduleName in expected do
    unless env.header.moduleNames.any (fun name => name.toString == moduleName) do
      throwError "Audit import missing: {{moduleName}}"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut violations : Array Json := #[]
  let mut declarations : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx]!.toString
    unless expected.contains moduleName do continue
    checked := checked + 1
    declarations := declarations.push <| Json.mkObj [
      ("module", toJson moduleName), ("name", toJson name.toString),
      ("theorem", toJson info.isTheorem)]
    if info.isTheorem then theorems := theorems + 1
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => {standard}
    unless bad.isEmpty do
      violations := violations.push <| Json.mkObj [
        ("module", toJson moduleName),
        ("declaration", toJson name.toString),
        ("axioms", toJson (bad.map Name.toString))]
  let report := Json.mkObj [
    ("modules", toJson expected),
    ("declarations_checked", toJson checked),
    ("theorems_checked", toJson theorems),
    ("declarations", toJson declarations),
    ("violations", toJson violations)]
  liftIO <| IO.FS.writeFile {json.dumps(str(report))} report.pretty
"""


def audit_groups(package: Path, modules: list[str]) -> list[dict]:
    """Split conflicting executable namespaces without skipping any module."""
    with tempfile.TemporaryDirectory(prefix="near-lean-axiom-audit-") as temp:
        source = Path(temp) / "NearLeanAxiomAudit.lean"
        report = Path(temp) / "report.json"
        source.write_text(audit_source(modules, report))
        local = package / ".lake/build/lib/lean"
        for module in modules:
            artifact = local.joinpath(*module.split(".")).with_suffix(".olean")
            if not artifact.is_file():
                raise FileNotFoundError(f"missing local audit artifact: {artifact}")
        # Lake puts dependency libraries before this package in LEAN_PATH.
        # Executable roots often share names (Tests.Main), and case-insensitive
        # filesystems also alias tests.Main. Audit our own artifacts first.
        search = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                                cwd=package, text=True, capture_output=True, check=True)
        lean_path = str(local) + os.pathsep + search.stdout.strip()
        process = subprocess.run(["lake", "env", "env", f"LEAN_PATH={lean_path}",
                                  "lean", str(source)],
                                 cwd=package, text=True, capture_output=True)
        if process.returncode == 0:
            return [json.loads(report.read_text())]
        if "environment already contains" in process.stdout and len(modules) > 1:
            mid = len(modules) // 2
            return (audit_groups(package, modules[:mid]) +
                    audit_groups(package, modules[mid:]))
        print(process.stdout, end="", file=sys.stderr)
        print(process.stderr, end="", file=sys.stderr)
        raise subprocess.CalledProcessError(process.returncode, process.args)


def failing_violations(violations: list[dict], allow_sorry: bool,
                       require_clean_modules: list[str],
                       allow_sorry_modules: Sequence[str] = ()) -> list[dict]:
    """Completed modules stay strict even inside a package with open proofs."""
    return [v for v in violations if not (
        (allow_sorry or v["module"] in allow_sorry_modules) and v["axioms"] == ["sorryAx"]
        and v["module"] not in require_clean_modules)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("package", type=Path, help="Lake package directory")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--no-build", action="store_true",
                        help="Use existing package artifacts; missing modules still fail")
    parser.add_argument("--allow-sorry", action="store_true",
                        help="Tolerate sorryAx (open proofs); still fail on any other axiom")
    parser.add_argument("--allow-sorry-module", action="append", default=[],
                        help="Tolerate sorryAx only in this module; repeatable, missing modules fail")
    parser.add_argument("--require-clean-module", action="append", default=[],
                        help="Keep this module strict even with --allow-sorry; repeatable")
    args = parser.parse_args()
    if args.allow_sorry and args.allow_sorry_module:
        parser.error("--allow-sorry cannot be combined with --allow-sorry-module")
    root = Path(__file__).resolve().parent.parent
    package = args.package.resolve()
    report = args.report.resolve()
    if not package.is_relative_to(root):
        parser.error("package must be inside this repository")
    if not any((package / name).is_file()
               for name in ("lakefile.toml", "lakefile.lean")):
        parser.error("package has no Lake manifest")
    modules = source_modules(root, package)
    if not modules:
        parser.error("package has no Lean source modules")
    missing = set(args.require_clean_module) - set(modules)
    if missing:
        parser.error("required clean module is absent: " + ", ".join(sorted(missing)))
    missing = set(args.allow_sorry_module) - set(modules)
    if missing:
        parser.error("allowed sorry module is absent: " + ", ".join(sorted(missing)))
    report.parent.mkdir(parents=True, exist_ok=True)
    report.unlink(missing_ok=True)
    if not args.no_build:
        subprocess.run(["lake", "build", *modules], cwd=package, check=True)
    groups = audit_groups(package, modules)
    declarations = [d for group in groups for d in group["declarations"]]
    violations = [v for group in groups for v in group["violations"]]
    failing = failing_violations(violations, args.allow_sorry, args.require_clean_module,
                                 args.allow_sorry_module)
    tolerated = [v for v in violations if v not in failing]
    result = {
        "modules": modules,
        "declarations_checked": len(declarations),
        "theorems_checked": sum(d["theorem"] for d in declarations),
        "allow_sorry": args.allow_sorry,
        "allow_sorry_modules": args.allow_sorry_module,
        "require_clean_modules": args.require_clean_module,
        "violations": violations,
    }
    report.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{package.relative_to(root)}: {len(modules)} modules, "
          f"{result['declarations_checked']} declarations, "
          f"{result['theorems_checked']} theorems, "
          f"{len(violations)} violations"
          + (f" ({len(tolerated)} sorry, tolerated)" if args.allow_sorry or args.allow_sorry_module else ""))
    for v in violations:
        tag = "sorry" if v in tolerated else "FAIL"
        print(f"  {tag}: {v['declaration']}  [{', '.join(v['axioms'])}]")
    print(f"Full report: {report}")
    return int(bool(failing))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
    except OSError as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        sys.exit(2)
