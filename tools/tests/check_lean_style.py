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
        cwd=root / "near-lean/vm", text=True, capture_output=True,
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
    multilingual = '''def text : String := "日本語 🙂"
def escaped : String := "quote: \\\"日本語"
def raw : String := r##"quote: " 日本語 🙂 /- literal -/"##
def character : Char := '日'
'''.encode()
    source.write_bytes(multilingual)
    result = run(source, fix=True)
    assert result.returncode == 0, result.stdout + result.stderr
    assert source.read_bytes() == multilingual, "style fix changed Unicode literal bytes"
    outside = '''/- A comment with "quotes" and /- a nested comment -/. -/
def text : String := "backslash: \\\\"
def 日本語 : Nat := 1
'''.encode()
    source.write_bytes(outside)
    result = run(source)
    assert result.returncode == 1, result.stdout + result.stderr
    assert "ERR_UNICODE" in result.stdout, result.stdout
    assert source.read_bytes() == outside, "check mode changed Unicode source"
print("Lean style integration checks passed.")
