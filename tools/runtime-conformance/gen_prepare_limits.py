#!/usr/bin/env python3
"""Generate the prepare-limit fixtures: one module per case, at and over each
`prepare_v3` limit of protocol 86, plus the rejected import kinds.

Some modules are large (a 196 KiB function body, 10 000 functions), so the
`.wasm` files are committed and their WAT is produced here, not checked in.
Run from the repository root with the pinned wasm-tools:

    python3 tools/runtime-conformance/gen_prepare_limits.py
"""

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

FIXTURES = Path(__file__).resolve().parent / "fixtures"
# protocol 86 limit_config
TYPES, FUNCTIONS, LOCALS, BODY, TABLE_ELEMENTS = 1024, 10_000, 1_000_000, 196_608, 10_000
# wasmparser allows at most 50 000 locals per function. A module at the locals
# limit is not compared: Wasmtime itself fails to compile one.
LOCALS_PER_FUNCTION = 50_000
METHOD = '(func (export "f"))'


def body_of_size(size):
    """A function whose code entry (locals vector, expression, end) is `size` bytes."""
    # 1 byte for the empty locals vector, 1 for `end`, the rest `nop`s.
    return "(func " + "nop " * (size - 2) + ")"


def distinct_types(n):
    """`n` type-section entries; wasm-tools keeps repeated explicit types."""
    return "(type (func))\n" * n


CASES = {
    "types_at_limit": distinct_types(TYPES) + METHOD,
    "types_over_limit": distinct_types(TYPES + 1) + METHOD,
    "functions_at_limit": "(func)\n" * (FUNCTIONS - 1) + METHOD,
    "functions_over_limit": "(func)\n" * FUNCTIONS + METHOD,
    "imported_functions_over_limit": '(import "env" "panic" (func))\n' * FUNCTIONS + METHOD,
    "locals_over_limit": f"(func (local {'i32 ' * LOCALS_PER_FUNCTION}))\n" * (LOCALS // LOCALS_PER_FUNCTION)
        + "(func (local i32))\n" + METHOD,
    "body_at_limit": body_of_size(BODY) + METHOD,
    "body_over_limit": body_of_size(BODY + 1) + METHOD,
    "tables_over_limit": "(table 0 funcref) (table 0 funcref)\n" + METHOD,
    "table_elements_at_limit": f"(table {TABLE_ELEMENTS} funcref)\n" + METHOD,
    "table_elements_over_limit": f"(table {TABLE_ELEMENTS + 1} funcref)\n" + METHOD,
    "import_other_module": '(import "other" "panic" (func))\n' + METHOD,
    "import_global": '(import "env" "g" (global i32))\n' + METHOD,
    "import_table": '(import "env" "t" (table 0 funcref))\n' + METHOD,
    "import_memory": '(import "env" "memory" (memory 1))\n' + METHOD,
}


def main():
    calls = []
    with tempfile.TemporaryDirectory() as temp:
        for name, body in CASES.items():
            wat = Path(temp) / f"{name}.wat"
            wat.write_text(f"(module\n{body}\n)\n")
            wasm = FIXTURES / f"prepare_{name}.wasm"
            subprocess.run(["wasm-tools", "parse", str(wat), "-o", str(wasm)], check=True)
            fixture = {
                "code": f"tools/runtime-conformance/fixtures/{wasm.name}",
                "sha256": hashlib.sha256(wasm.read_bytes()).hexdigest(),
                "protocolVersion": 86, "initialBalance": "100000000000000000000000000",
                "storage": [], "calls": [{"name": f"prepare: {name}", "method": "f", "args": {}}],
            }
            (FIXTURES / f"prepare_{name}.json").write_text(json.dumps(fixture, indent=2) + "\n")
            calls.append(name)
    print(f"wrote {len(calls)} prepare-limit fixtures")


if __name__ == "__main__":
    main()
