#!/usr/bin/env python3
"""Audit every source module in a Lake package for nonstandard axioms.

The gate for a finished proof: every declaration may depend only on the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). In particular
no `sorryAx` (an open proof) and no `Lean.ofReduceBool` (`native_decide`,
which trusts the compiler rather than the kernel).

Usage:
  tools/axiom-audit.py near-lean/wasm --report audit/wasm.json
  tools/axiom-audit.py near-lean/vm --report audit/vm.json --no-build

Unlike an umbrella import or a source grep, this checks the transitive axiom
dependencies of every declaration, including private helpers and proof fields
in definitions. Untracked, nonignored Lean sources are included. Nested Lake
packages must be audited separately. A missing module or failed build is an
audit failure, never an exemption.

`--allow-sorry` tolerates `sorryAx` alone, for packages whose proofs are
intentionally left open; the sorried declarations are listed, and every other
nonstandard axiom still fails. Repeat --require-clean-module to keep completed
modules strict within such a package; a missing required module is an audit
error. Use --allow-sorry-module instead of --allow-sorry to limit open proofs
to named modules while keeping every other module strict.
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
MANIFESTS = ("lakefile.toml", "lakefile.lean")


def source_modules(root: Path, package: Path) -> list[str]:
    """Module names of the package's own Lean sources, nested packages excluded."""
    listing = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others",
         "--exclude-standard", "--", "*.lean"],
        check=True, stdout=subprocess.PIPE,
    )
    modules: set[str] = set()
    for entry in listing.stdout.decode().split("\0"):
        if not entry:
            continue
        path = root / entry
        # A cached entry may be deleted on disk but not yet staged; audit what exists.
        if not path.is_file() or not path.is_relative_to(package):
            continue
        relative = path.relative_to(package)
        nested = any(
            (package / parent / manifest).exists()
            for parent in relative.parents if parent != Path(".")
            for manifest in MANIFESTS
        )
        if nested:
            continue
        modules.add(".".join(relative.with_suffix("").parts))
    return sorted(modules)


def audit_source(modules: list[str], report: Path) -> str:
    """A Lean script that imports the modules and writes their axiom report as JSON."""
    header = "\n".join(f"import {module}" for module in modules)
    names = ", ".join(json.dumps(module) for module in modules)
    nonstandard = " && ".join(f"ax != `{name}" for name in STANDARD_AXIOMS)
    return f"""{header}
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let audited : Array String := #[{names}]
  for module in audited do
    unless env.header.moduleNames.any (fun name => name.toString == module) do
      throwError "audited module is not imported: {{module}}"
  let mut rows : Array Json := #[]
  let mut violations : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let module := env.header.moduleNames[index]!.toString
    unless audited.contains module do continue
    rows := rows.push <| Json.mkObj [
      ("module", toJson module), ("name", toJson name.toString),
      ("theorem", toJson info.isTheorem)]
    let axioms ← collectAxioms name
    let offending := axioms.filter fun ax => {nonstandard}
    unless offending.isEmpty do
      violations := violations.push <| Json.mkObj [
        ("module", toJson module), ("declaration", toJson name.toString),
        ("axioms", toJson (offending.map Name.toString))]
  let report := Json.mkObj [
    ("modules", toJson audited), ("declarations", toJson rows),
    ("violations", toJson violations)]
  liftIO <| IO.FS.writeFile {json.dumps(str(report))} report.pretty
"""


def audit_groups(package: Path, modules: list[str]) -> list[dict]:
    """Run the audit script, splitting the module list when two executable
    roots define the same declarations. Every module is audited exactly once."""
    artifacts = package / ".lake/build/lib/lean"
    for module in modules:
        olean = artifacts.joinpath(*module.split(".")).with_suffix(".olean")
        if not olean.is_file():
            raise FileNotFoundError(f"missing local audit artifact: {olean}")
    with tempfile.TemporaryDirectory(prefix="safe-near-axiom-audit-") as scratch:
        script = Path(scratch) / "AxiomAudit.lean"
        report = Path(scratch) / "report.json"
        script.write_text(audit_source(modules, report))
        # Put this package's own artifacts first: dependency executables can
        # share root names (Tests.Main), and the audit must see the local ones.
        env = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=package,
                             text=True, capture_output=True, check=True)
        lean_path = str(artifacts) + os.pathsep + env.stdout.strip()
        run = subprocess.run(["lake", "env", "env", f"LEAN_PATH={lean_path}", "lean", str(script)],
                             cwd=package, text=True, capture_output=True)
        if run.returncode == 0:
            return [json.loads(report.read_text())]
        if "environment already contains" in run.stdout and len(modules) > 1:
            half = len(modules) // 2
            return audit_groups(package, modules[:half]) + audit_groups(package, modules[half:])
        sys.stderr.write(run.stdout)
        sys.stderr.write(run.stderr)
        raise subprocess.CalledProcessError(run.returncode, run.args)


def failing_violations(violations: list[dict], allow_sorry: bool,
                       require_clean_modules: list[str],
                       allow_sorry_modules: Sequence[str] = ()) -> list[dict]:
    """The violations that fail the audit: everything except a lone `sorryAx`
    in a module where open proofs are tolerated and not required to be clean."""
    def tolerated(violation: dict) -> bool:
        open_allowed = allow_sorry or violation["module"] in allow_sorry_modules
        return (open_allowed and violation["axioms"] == ["sorryAx"]
                and violation["module"] not in require_clean_modules)
    return [violation for violation in violations if not tolerated(violation)]


def parse_arguments() -> argparse.Namespace:
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
    root = Path(__file__).resolve().parents[1]
    args.root = root
    args.package = args.package.resolve()
    args.report = args.report.resolve()
    if not args.package.is_relative_to(root):
        parser.error("package must be inside this repository")
    if not any((args.package / manifest).is_file() for manifest in MANIFESTS):
        parser.error("package has no Lake manifest")
    args.modules = source_modules(root, args.package)
    if not args.modules:
        parser.error("package has no Lean source modules")
    for option, requested in (("required clean", args.require_clean_module),
                              ("allowed sorry", args.allow_sorry_module)):
        absent = sorted(set(requested) - set(args.modules))
        if absent:
            parser.error(f"{option} module is absent: " + ", ".join(absent))
    return args


def main() -> int:
    args = parse_arguments()
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.unlink(missing_ok=True)
    if not args.no_build:
        subprocess.run(["lake", "build", *args.modules], cwd=args.package, check=True)
    groups = audit_groups(args.package, args.modules)
    declarations = [row for group in groups for row in group["declarations"]]
    violations = [row for group in groups for row in group["violations"]]
    failing = failing_violations(violations, args.allow_sorry, args.require_clean_module,
                                 args.allow_sorry_module)
    tolerated = [row for row in violations if row not in failing]
    result = {
        "modules": args.modules,
        "declarations_checked": len(declarations),
        "theorems_checked": sum(row["theorem"] for row in declarations),
        "allow_sorry": args.allow_sorry,
        "allow_sorry_modules": args.allow_sorry_module,
        "require_clean_modules": args.require_clean_module,
        "violations": violations,
    }
    args.report.write_text(json.dumps(result, indent=2) + "\n")
    lenient = args.allow_sorry or args.allow_sorry_module
    print(f"{args.package.relative_to(args.root)}: {len(args.modules)} modules, "
          f"{result['declarations_checked']} declarations, "
          f"{result['theorems_checked']} theorems, {len(violations)} violations"
          + (f" ({len(tolerated)} sorry, tolerated)" if lenient else ""))
    for violation in violations:
        tag = "sorry" if violation in tolerated else "FAIL"
        print(f"  {tag}: {violation['declaration']}  [{', '.join(violation['axioms'])}]")
    print(f"Full report: {args.report}")
    return int(bool(failing))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
    except OSError as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        sys.exit(2)
