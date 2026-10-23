import Wasm.Binary

/-!
# Text format, through `wasm-tools`

There is no WAT parser in Lean. Tests that write modules as text compile
them with `wasm-tools parse` at run time and decode the bytes. This is an
`IO` convenience for test harnesses, never part of a semantics.
-/

namespace Wasm.Wat

/-- Compile WAT text to a module with `wasm-tools parse`. -/
def compile (text : String) : IO (Except String Module) := do
  let dir ← IO.FS.createTempDir
  let src := dir / "module.wat"
  let out := dir / "module.wasm"
  IO.FS.writeFile src text
  let result ← IO.Process.output
    { cmd := "wasm-tools", args := #["parse", src.toString, "-o", out.toString] }
  if result.exitCode != 0 then
    IO.FS.removeDirAll dir
    return .error s!"wasm-tools parse failed: {result.stderr.trimAsciiEnd}"
  let bytes ← IO.FS.readBinFile out
  IO.FS.removeDirAll dir
  return match Binary.decode bytes with
    | .ok m => .ok m
    | .error e => .error e.message

/-- Compile, or throw. -/
def compile! (text : String) : IO Module := do
  match ← compile text with
  | .ok m => return m
  | .error e => throw (IO.userError e)

end Wasm.Wat
