import Wasm.Binary
import Wasm.Validate

/-!
# `wasm`: command-line front end

    lake exe wasm decode FILE.wasm     decode and print a summary of the module
    lake exe wasm validate FILE.wasm   decode and validate

More commands (validate, run) arrive with the corresponding modules.
-/

namespace Wasm.Cli

def summary (m : Module) : String :=
  s!"types {m.types.size}, imports {m.imports.size}, funcs {m.funcs.size}, " ++
  s!"tables {m.tables.size}, mems {m.mems.size}, globals {m.globals.size}, " ++
  s!"exports {m.exports.size}, elems {m.elems.size}, datas {m.datas.size}, " ++
  s!"start {m.start}"

def decodeCommand (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  match Binary.decode bytes with
  | .ok m => IO.println s!"ok: {summary m}"; return 0
  | .error (.malformed pos msg) => IO.println s!"malformed: {msg} (byte {pos})"; return 1
  | .error (.unsupported pos f) => IO.println s!"unsupported: {f} (byte {pos})"; return 2

def validateCommand (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  match Binary.decode bytes with
  | .error e => IO.println e.message; return 1
  | .ok m =>
    match m.validate .all with
    | .ok _ => IO.println "valid"; return 0
    | .error e => IO.println s!"invalid: {e.message}"; return 1

def usage : String := "Usage: lake exe wasm (decode | validate) FILE.wasm"

def main : List String → IO UInt32
  | ["decode", path] => decodeCommand path
  | ["validate", path] => validateCommand path
  | _ => do IO.eprintln usage; return 3

end Wasm.Cli

def main := Wasm.Cli.main
