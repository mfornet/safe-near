"""Exercise the real pinned formatter on a tiny independent Lake package."""

from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_format


binary, environment = lean_format.formatter()
with tempfile.TemporaryDirectory(prefix="safe-near-formatter-test-") as directory:
    root = Path(directory)
    (root / "lean-toolchain").write_text((lean_format.ROOT / "lean-toolchain").read_text())
    (root / "lakefile.toml").write_text('name = "FormatFixture"\n[[lean_lib]]\nname = "Example"\n')
    (root / "lean-fmt.toml").write_text('[format]\nline-width = 100\n')
    source = root / "Example.lean"
    dirty = ('-- Preserve this comment.\n'
             'def value(x:Nat):Nat:=x+1\n'
             'def text : String := "(module ;; comment)"\n'
             'theorem value_zero:value 0=1:=by rfl\n')
    source.write_text(dirty)
    groups = {Path("."): [Path("Example.lean")]}
    assert lean_format.run_groups(root, groups, binary, environment) == 1
    assert source.read_text() == dirty, "check mode changed source"
    assert lean_format.run_groups(root, groups, binary, environment, mode="fix") == 0
    formatted = source.read_text()
    assert formatted != dirty, "syntax formatter did not format the fixture"
    assert '-- Preserve this comment.' in formatted
    assert '"(module ;; comment)"' in formatted, "formatter changed a string literal"
    assert "sorry" not in formatted
    assert lean_format.run_groups(root, groups, binary, environment) == 0
    assert source.read_text() == formatted, "formatting was not stable"
    subprocess.run(["lake", "build", "Example"], cwd=root, env=environment, check=True)
print("Validated syntax-formatting integration checks passed.")
