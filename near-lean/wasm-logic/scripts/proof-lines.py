#!/usr/bin/env python3
"""Compare the size of the stack proofs with Iris-Wasm's (criterion S3.4).

    scripts/proof-lines.py <iriswasm checkout>

Counts the non-blank, non-comment lines of every proved statement: Rocq
`Lemma`/`Theorem` blocks up to `Qed.`, Lean `theorem` declarations up to the
next top-level item. Each Rocq file of `theories/iris/examples/stack/function`
is compared with the Lean theorems that port it (the table below); shared
helpers count on the `stack_common.v` row on both sides.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = [ROOT / "WasmLogic/Examples/Stack/Specs.lean", ROOT / "WasmLogic/Examples/Stack/Map.lean"]

GROUPS = {
    "new_stack.v": ["page_split", "spec_new_stack"],
    "is_empty.v": ["spec_is_empty_op", "spec_is_empty"],
    "is_full.v": ["spec_is_full_op", "spec_is_full"],
    "push.v": ["stack_elems_succ", "spec_push_op", "spec_push"],
    "pop.v": ["spec_pop_op", "spec_pop"],
    "stack_length.v": ["spec_stack_length_op", "spec_stack_length"],
    "stack_map.v": ["stackElems_append", "stackElems_single", "stackElems_mid", "stackAll2_cons",
                    "stackAll_snoc", "spec_map_loop", "isStack_intro", "spec_map_op", "spec_stack_map"],
}

TOP = re.compile(r"^(theorem|lemma|def|abbrev|structure|instance|section|end|namespace|open|variable|/--|/-!|@\[)")


def code_lines(lines):
    """Non-blank lines, without Lean `--` or Rocq `(* *)` single-line comments."""
    out = []
    for line in lines:
        s = line.strip()
        if not s or s.startswith("--") or (s.startswith("(*") and s.endswith("*)")):
            continue
        out.append(s)
    return len(out)


def lean_theorems():
    sizes = {}
    for path in LEAN:
        lines = path.read_text().splitlines()
        i = 0
        while i < len(lines):
            m = re.match(r"^theorem (\S+)", lines[i])
            if not m:
                i += 1
                continue
            j = i + 1
            while j < len(lines) and not TOP.match(lines[j]):
                j += 1
            sizes[m.group(1)] = code_lines(lines[i:j])
            i = j
    return sizes


def rocq_lemmas(path):
    total, inside, block = 0, False, []
    for line in path.read_text().splitlines():
        if re.match(r"^\s*(Lemma|Theorem)\s", line):
            inside, block = True, []
        if inside:
            block.append(line)
            if re.search(r"\b(Qed|Defined|Admitted)\.\s*$", line):
                total += code_lines(block)
                inside = False
    return total


def main():
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    rocq_dir = Path(sys.argv[1]) / "theories/iris/examples/stack/function"
    lean = lean_theorems()
    grouped = {n for names in GROUPS.values() for n in names}
    rows = []
    for rfile, names in GROUPS.items():
        rows.append((rfile, rocq_lemmas(rocq_dir / rfile), sum(lean[n] for n in names)))
    common = sum(v for n, v in lean.items() if n not in grouped)
    rows.append(("stack_common.v", rocq_lemmas(rocq_dir / "stack_common.v"), common))
    print("| Rocq file | Rocq lines | Lean lines | Lean / Rocq |")
    print("|---|---:|---:|---:|")
    for rfile, r, l in rows:
        print(f"| `{rfile}` | {r} | {l} | {l / r:.2f} |")
    rt, lt = sum(r for _, r, _ in rows), sum(l for _, _, l in rows)
    print(f"| total | {rt} | {lt} | {lt / rt:.2f} |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
