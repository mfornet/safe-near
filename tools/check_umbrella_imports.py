#!/usr/bin/env python3
"""Keep test executables and contract projects from building proofs they never use.

`Wasm`, `NearVM`, `NearRuntime` and `NearChain` are umbrella modules: they
import the executable code of their package together with every theorem about
it. A module that imports an umbrella makes everything downstream elaborate
those theorems, so `lake build vm-tests` used to build the whole VM proof
corpus before running a single scenario (SAF-64). Repository sources import
the modules they use instead; only the umbrella files themselves list the
package.
"""

import argparse
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_toolchains import repository_files  # noqa: E402

UMBRELLAS = {
    "Wasm": Path("near-lean/wasm/Wasm.lean"),
    "NearVM": Path("near-lean/vm/NearVM.lean"),
    "NearRuntime": Path("near-lean/runtime/NearRuntime.lean"),
    "NearChain": Path("near-lean/chain/NearChain.lean"),
}
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)")


def check(root: Path) -> list[str]:
    allowed = set(UMBRELLAS.values())
    errors = []
    for file in repository_files(root):
        if file.suffix != ".lean" or file in allowed or not (root / file).is_file():
            continue
        for number, line in enumerate((root / file).read_text().splitlines(), 1):
            match = IMPORT.match(line)
            if match and match[1] in UMBRELLAS:
                errors.append(f"{file}:{number}: imports the umbrella `{match[1]}`; "
                              "import the modules it uses")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    errors = check(args.root)
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    print(f"No repository module imports {', '.join(sorted(UMBRELLAS))} as a whole.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
