"""Integration checks for the real Lean linter; needs the pinned Mathlib cache."""

from pathlib import Path
import subprocess
import tempfile


root = Path(__file__).resolve().parents[2]
driver = root / "tools/LeanStyle.lean"


def run(path, fix=False):
    return subprocess.run(
        ["lake", "env", "lean", "--run", str(driver),
         *(["--fix"] if fix else []), str(path)],
        cwd=root / "near-lean/wasm", text=True, capture_output=True,
    )


with tempfile.TemporaryDirectory() as directory:
    source = Path(directory) / "Example.lean"
    dirty = b'def example : Nat := 1  \r\n'
    source.write_bytes(dirty)
    check = run(source)
    assert check.returncode == 1, check.stdout + check.stderr
    assert source.read_bytes() == dirty, "check mode rewrote the file"
    assert "ERR_" in check.stdout, check.stdout
    fixed = run(source, fix=True)
    assert fixed.returncode == 0, fixed.stdout + fixed.stderr
    assert source.read_bytes() == b'def example : Nat := 1\n'
    first = source.read_bytes()
    assert run(source, fix=True).returncode == 0
    assert source.read_bytes() == first, "formatting is not idempotent"
    assert run(source).returncode == 0
    literal = b'def text : String := "(module ;; comment)"\n'
    source.write_bytes(literal)
    assert run(source, fix=True).returncode == 0
    assert source.read_bytes() == literal, "formatter changed a WAT string literal"
print("Lean style integration checks passed.")
