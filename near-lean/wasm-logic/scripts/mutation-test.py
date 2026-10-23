#!/usr/bin/env python3
"""Check that the examples' specifications are strong enough to catch bugs.

Each mutant changes one instruction of the stack module or of its client, in
the Lean definitions the specifications are proved about, and the mutant is
killed if a proof about it fails. Changes to the bytes themselves are caught
already: `stack_decodes` and `client_decodes` pin the definitions to the
bytes. So that only the specifications can kill a mutant, those two theorems
are stubbed out with `sorry` while this runs (and a baseline run with only
the stubs must pass).

    scripts/mutation-test.py [--only N]

Every mutant here changes what the code does; none is equivalent to the
original. The files are restored afterwards, also on failure. Takes a few
minutes: each mutant rebuilds the specification modules.
"""

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STACK = ROOT / "WasmLogic/Examples/Stack/Code.lean"
CLIENT = ROOT / "WasmLogic/Examples/Client/Code.lean"
TARGETS = ["WasmLogic.Examples.Stack.Specs", "WasmLogic.Examples.Stack.Map",
           "WasmLogic.Examples.Client.Main"]
PROOF_FILES = ["WasmLogic/Examples/Stack/Specs.lean", "WasmLogic/Examples/Stack/Map.lean",
               "WasmLogic/Examples/Client/Main.lean"]

# Each stub replaces a decode theorem's proof.
STUBS = [
    (STACK, "theorem stack_decodes : Binary.decode stackBytes = .ok stackModule := by\n  kernel_rfl",
     "theorem stack_decodes : Binary.decode stackBytes = .ok stackModule := by\n  sorry"),
    (CLIENT, "theorem client_decodes : Binary.decode clientBytes = .ok clientModule := by\n  kernel_rfl",
     "theorem client_decodes : Binary.decode clientBytes = .ok clientModule := by\n  sorry"),
]

# (description, file, old, new): `old` occurs exactly once in `file`.
MUTANTS = [
    ("is_empty compares with ne", STACK,
     ".load .i32 none a0, .i32_relop .eq]", ".load .i32 none a0, .i32_relop .ne]"),
    ("is_full checks the wrong offset", STACK, ".i32_const 65532", ".i32_const 65528"),
    ("push moves the pointer by 8", STACK,
     ".load .i32 none a0, .i32_const 4, .i32_binop .add", ".load .i32 none a0, .i32_const 8, .i32_binop .add"),
    ("push stores the address, not the value", STACK,
     ".local_get 1, .store .i32 none a0,", ".local_get 0, .store .i32 none a0,"),
    ("push does not update the pointer", STACK,
     ".local_get 0, .local_get 2, .store .i32 none a0]", ".local_get 0, .local_get 0, .store .i32 none a0]"),
    ("pop moves the pointer up", STACK,
     ".i32_const 4, .i32_binop .sub, .store", ".i32_const 4, .i32_binop .add, .store"),
    ("pop returns the address, not the value", STACK,
     ".local_tee 1, .load .i32 none a0,", ".local_tee 1,"),
    ("stack_length takes a remainder", STACK, ".i32_binop .div_u", ".i32_binop .rem_u"),
    ("new_stack grows by two pages", STACK, "[.i32_const 1, .memory_grow", "[.i32_const 2, .memory_grow"),
    ("new_stack computes the address wrongly", STACK,
     ".i32_const 65536, .i32_binop .mul", ".i32_const 32768, .i32_binop .mul"),
    ("new_stack returns 0 on failure", STACK,
     "[.i32_const 0xFFFFFFFF]\n", "[.i32_const 0]\n"),
    ("validate_stack traps on valid stacks", STACK,
     ".«if» .empty [.unreachable] []]", ".«if» .empty [] [.unreachable]]"),
    ("stack_map stops at once", STACK,
     ".local_get 2, .local_get 3, .i32_relop .eq, .br_if 1", ".local_get 2, .local_get 3, .i32_relop .ne, .br_if 1"),
    ("stack_map steps by 8", STACK,
     ".local_get 2, .i32_const 4, .i32_binop .add", ".local_get 2, .i32_const 8, .i32_binop .add"),
    ("stack_map calls the table entry named by the stack", STACK,
     ".local_get 1, .call_indirect 1 0", ".local_get 0, .call_indirect 1 0"),
    ("stack_map starts at the top", STACK,
     ".local_set 3, .local_get 0, .local_set 2", ".local_set 3, .local_get 3, .local_set 2"),
    ("client pushes 7", CLIENT, ".i32_const 6", ".i32_const 7"),
    ("client adds the popped values", CLIENT, ".call 2, .i32_binop .sub", ".call 2, .i32_binop .add"),
    ("client returns 0 when new_stack fails", CLIENT,
     "[.i32_const 0xFFFFFFFF]\n", "[.i32_const 0]\n"),
]


def build() -> tuple[bool, str]:
    r = subprocess.run(["lake", "build", *TARGETS], cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0, r.stdout + r.stderr


def proof_errors(log: str) -> list[str]:
    return [line for line in log.splitlines()
            if line.startswith("error:") and any(p in line for p in PROOF_FILES)]


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text()
    if text.count(old) != 1:
        raise SystemExit(f"{path.name}: {old!r} occurs {text.count(old)} times, expected once")
    path.write_text(text.replace(old, new))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", type=int, help="run only mutant N (1-based)")
    args = ap.parse_args()

    originals = {p: p.read_text() for p in (STACK, CLIENT)}
    for desc, path, old, _ in MUTANTS:
        if originals[path].count(old) != 1:
            raise SystemExit(f"mutant {desc!r}: {old!r} occurs {originals[path].count(old)} times in {path.name}")
    survivors = []
    try:
        for path, old, new in STUBS:
            replace_once(path, old, new)
        stubbed = {p: p.read_text() for p in (STACK, CLIENT)}
        ok, log = build()
        if not ok:
            print(log)
            print("baseline (decode theorems stubbed, no mutation) does not build", file=sys.stderr)
            return 1
        print("baseline builds")
        for i, (desc, path, old, new) in enumerate(MUTANTS, 1):
            if args.only and i != args.only:
                continue
            for p, text in stubbed.items():
                p.write_text(text)
            replace_once(path, old, new)
            ok, log = build()
            errs = proof_errors(log)
            if ok or not errs:
                survivors.append(desc)
                print(f"{i:2}. SURVIVED  {desc}")
            else:
                where = errs[0].split(": ", 1)[1].split(" ", 1)[0]
                print(f"{i:2}. killed    {desc}  ({where})")
    finally:
        for p, text in originals.items():
            p.write_text(text)
        subprocess.run(["lake", "build", *TARGETS], cwd=ROOT, capture_output=True)
    if survivors:
        print(f"{len(survivors)} mutant(s) survived", file=sys.stderr)
        return 1
    print("every mutant was killed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
