"""Fast checks of near-lean/wasm-logic that need no Lean build.

The proofs themselves are checked by `lake build --wfail` (with the rule
coverage check and the decode theorems) in the wasm-logic workflow and the
periodic check; these catch, in seconds, the ways the package can drift
without a proof noticing: stale byte literals, a module the build no longer
reaches, an escape hatch, a coverage table or mutation suite that no longer
matches the code, a dependency beyond the Wasm level.
"""

import importlib.util
from pathlib import Path
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / "near-lean/wasm-logic"
SRC = PKG / "WasmLogic"

# (directory, .wasm base name, Lean namespace, definition) of every example compiled from .wat.
EXAMPLES = [
    ("Examples/Stack", "stack", "WasmLogic.Examples.Stack", "stackBytes"),
    ("Examples/Client", "client", "WasmLogic.Examples.Client", "clientBytes"),
    ("Examples/Probe", "probe", "WasmLogic.Examples.Probe", "probeBytes"),
]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_files():
    return sorted(SRC.rglob("*.lean"))


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


class WasmLogicTests(unittest.TestCase):
    def test_byte_literals_match_committed_binaries(self):
        script = PKG / "scripts/wasm-bytes.py"
        for directory, base, namespace, name in EXAMPLES:
            wasm = SRC / directory / f"{base}.wasm"
            expected = subprocess.run([sys.executable, script, wasm, namespace, name],
                                      check=True, capture_output=True, text=True).stdout
            self.assertEqual((SRC / directory / "Bytes.lean").read_text(), expected,
                             f"{directory}/Bytes.lean is stale: run scripts/check-wasm-bytes.sh --write")
            self.assertTrue((SRC / directory / f"{base}.wat").exists())

    def test_every_module_is_built(self):
        # `lake build` builds what WasmLogic.lean reaches by imports.
        imported, todo = set(), ["WasmLogic"]
        while todo:
            path = PKG / (todo.pop().replace(".", "/") + ".lean")
            for module in re.findall(r"^import (WasmLogic\S*)$", path.read_text(), flags=re.M):
                if module not in imported:
                    imported.add(module)
                    todo.append(module)
        for path in lean_files():
            module = ".".join(path.relative_to(PKG).with_suffix("").parts)
            self.assertIn(module, imported, f"{module} is not imported by WasmLogic.lean")

    def test_no_escape_hatches(self):
        for path in lean_files() + [PKG / "WasmLogic.lean"]:
            code = strip_comments(path.read_text())
            for token in ["sorry", "admit", "native_decide", "axiom", "implemented_by", "extern"]:
                self.assertIsNone(re.search(rf"\b{token}\b", code), f"{path.name} uses {token}")

    def test_stack_specs_are_symbolic(self):
        # S3.3: the specifications step through the code with the rules; they
        # never run the machine on a concrete input.
        for name in ["Examples/Stack/Specs.lean", "Examples/Stack/Map.lean"]:
            code = strip_comments((SRC / name).read_text())
            for token in ["Exec.run", "Exec.step", "wp_run", "kernel_rfl", "native_decide"]:
                self.assertNotIn(token, code, f"{name} uses {token}")

    def test_wasm_level_only(self):
        # S1.5: the logic depends on the runtime and iris-lean alone.
        lakefile = (PKG / "lakefile.toml").read_text()
        requires = re.findall(r'^\[\[require\]\]\nname = "(\w+)"', lakefile, flags=re.M)
        self.assertEqual(sorted(requires), ["Wasm", "iris"])
        for path in lean_files():
            for module in re.findall(r"^import (\S+)", path.read_text(), flags=re.M):
                self.assertRegex(module, r"^(WasmLogic|Wasm|Iris|Lean)(\.|$)", f"{path.name} imports {module}")

    def test_iris_pin_matches_manifest(self):
        lakefile = (PKG / "lakefile.toml").read_text()
        manifest = (PKG / "lake-manifest.json").read_text()
        rev = re.search(r'rev = "([0-9a-f]{40})"', lakefile).group(1)
        self.assertIn(f'"rev": "{rev}"', manifest)

    def test_coverage_table_names_every_instruction(self):
        # Mirrors `#check_rule_coverage`, which fails the Lean build: every
        # constructor of `Wasm.Instr` has rules or is listed as out of scope.
        syntax = (ROOT / "near-lean/wasm/Wasm/Syntax.lean").read_text()
        block = re.search(r"^inductive Instr where\n(.*?)\nderiving", syntax, flags=re.S | re.M).group(1)
        constructors = {c.strip("«»") for c in re.findall(r"^\s+\| (\S+)", block, flags=re.M)}
        coverage = (SRC / "Coverage.lean").read_text()
        listed = re.findall(r"``Wasm\.Instr\.(\w+)", coverage)
        self.assertEqual(len(listed), len(set(listed)), "an instruction is listed twice")
        self.assertEqual(set(listed), constructors)

    def test_mutants_still_apply(self):
        mutation = load("mutation_test", PKG / "scripts/mutation-test.py")
        self.assertGreaterEqual(len(mutation.MUTANTS), 10)
        for desc, path, old, new in mutation.MUTANTS:
            self.assertNotEqual(old, new)
            self.assertEqual(path.read_text().count(old), 1, f"mutant {desc!r} no longer applies")
        for path, old, _ in mutation.STUBS:
            self.assertEqual(path.read_text().count(old), 1, f"stub for {path.name} no longer applies")

    def test_notice_carries_iris_wasm_licence(self):
        notice = (PKG / "NOTICE").read_text()
        self.assertIn("https://github.com/logsem/iriswasm", notice)
        self.assertIn("Copyright (c) 2024 Logic and Semantics @ Aarhus University", notice)
        self.assertIn("MIT License", notice)


if __name__ == "__main__":
    unittest.main()
