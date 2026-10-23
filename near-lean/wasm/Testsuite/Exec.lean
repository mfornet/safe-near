import Wasm
import Lean.Data.Json

/-!
# Running one `.wast` script

`wasm-tools json-from-wast` splits a script into a JSON command list and one
`.wasm` (or `.wat`) file per module. We walk the commands against one store
that starts with the `spectest` host module, and record one outcome per
command. The outcomes form the coverage report CI diffs.

Outcomes:

- `pass`: the command behaved as the spec says.
- `fail`: it ran and the result was wrong. A bug.
- `decode_error`, `invalid_error`: a module the suite expects to be
  well-formed (valid) did not decode (validate), for a reason inside our
  feature scope. A bug.
- `out_of_scope:<feature>`: the module uses a feature we do not support
  (SIMD, GC, memory64, …). Expected, never a failure.
- `skipped:<kind>`: a command kind the driver does not run yet.
- `module_unavailable`: the command refers to a module that did not load.
-/

namespace Wasm.Testsuite

open Lean (Json)

inductive Outcome where
  | pass
  | fail (message : String)
  | decodeError (message : String)
  /-- A module the suite expects to be valid did not validate. A bug. -/
  | invalidError (message : String)
  | outOfScope (feature : String)
  | skipped (kind : String)
  | moduleUnavailable
deriving Repr, Inhabited

/-- The stable tag written to the coverage report. -/
def Outcome.tag : Outcome → String
  | .pass => "pass"
  | .fail _ => "fail"
  | .decodeError _ => "decode_error"
  | .invalidError _ => "invalid_error"
  | .outOfScope f => s!"out_of_scope:{f}"
  | .skipped k => s!"skipped:{k}"
  | .moduleUnavailable => "module_unavailable"

def Outcome.detail : Outcome → Option String
  | .fail m | .decodeError m | .invalidError m => some m
  | _ => none

/-- A bug, as opposed to unimplemented or out-of-scope coverage. -/
def Outcome.isFailure : Outcome → Bool
  | .fail _ | .decodeError _ | .invalidError _ => true
  | _ => false

structure CmdResult where
  line : Nat
  kind : String
  outcome : Outcome
deriving Repr, Inhabited

structure FileResult where
  path : String
  results : Array CmdResult := #[]
  /-- The script as a whole could not be run (tool failure, bad JSON). -/
  fileError : Option String := none
deriving Inhabited

/-! ## JSON access -/

private def str? (j : Json) (key : String) : Option String :=
  (j.getObjVal? key >>= Json.getStr?).toOption

private def nat? (j : Json) (key : String) : Option Nat :=
  (j.getObjVal? key >>= Json.getNat?).toOption

private def arr (j : Json) (key : String) : Array Json :=
  ((j.getObjVal? key >>= Json.getArr?).toOption).getD #[]

/-! ## Values

`json-from-wast` writes integers and float bit patterns as decimal strings,
NaN expectations as `nan:canonical` / `nan:arithmetic`, and references as
`null` or a number. -/

def parseValue (j : Json) : Except String Value := do
  let some ty := str? j "type" | throw "value without type"
  let some v := str? j "value" | throw "value without value"
  let num := fun (bits : Nat) => match v.toInt? with
    | some n => Except.ok (n % ((2 : Int) ^ bits)).toNat
    | none => Except.error s!"bad number {v}"
  match ty with
  | "i32" => return .i32 (UInt32.ofNat (← num 32))
  | "i64" => return .i64 (UInt64.ofNat (← num 64))
  | "f32" => return .f32 (UInt32.ofNat (← num 32))
  | "f64" => return .f64 (UInt64.ofNat (← num 64))
  | "funcref" => if v == "null" then return .ref (.null .funcref) else throw "funcref argument"
  | "externref" =>
    if v == "null" then return .ref (.null .externref) else return .ref (.extern (← num 64))
  | _ => throw s!"unsupported value type {ty}"

/-- What an `assert_return` expects for one result. -/
inductive Expected where
  | exact (v : Value)
  | nanCanonical (t : NumType)
  | nanArithmetic (t : NumType)
  /-- Any non-null reference of the type. -/
  | anyRef (t : RefType)
  /-- Any null reference. -/
  | anyNull

def parseExpected (j : Json) : Except String Expected := do
  let some ty := str? j "type" | throw "expected value without type"
  let v := (str? j "value").getD ""
  match ty, v with
  | "f32", "nan:canonical" => return .nanCanonical .f32
  | "f32", "nan:arithmetic" => return .nanArithmetic .f32
  | "f64", "nan:canonical" => return .nanCanonical .f64
  | "f64", "nan:arithmetic" => return .nanArithmetic .f64
  | "refnull", _ => return .anyNull
  | "funcref", "null" => return .exact (.ref (.null .funcref))
  | "funcref", _ => return .anyRef .funcref
  | "externref", "null" => return .exact (.ref (.null .externref))
  | "externref", _ => return .exact (← parseValue j)
  | "anyref", _ | "eqref", _ | "i31ref", _ | "structref", _ | "arrayref", _ | "nullref", _
  | "nullfuncref", _ | "nullexternref", _ | "exnref", _ | "v128", _ => throw "unsupported"
  | _, _ => return .exact (← parseValue j)

def isCanonicalNaN32 (b : UInt32) : Bool := b &&& 0x7FFFFFFF == 0x7FC00000
def isArithmeticNaN32 (b : UInt32) : Bool := b &&& 0x7FC00000 == 0x7FC00000
def isCanonicalNaN64 (b : UInt64) : Bool := b &&& 0x7FFFFFFFFFFFFFFF == 0x7FF8000000000000
def isArithmeticNaN64 (b : UInt64) : Bool := b &&& 0x7FF8000000000000 == 0x7FF8000000000000

def matchesExpected (e : Expected) (v : Value) : Bool :=
  match e, v with
  | .exact x, v => x == v
  | .nanCanonical .f32, .f32 b => isCanonicalNaN32 b
  | .nanArithmetic .f32, .f32 b => isArithmeticNaN32 b
  | .nanCanonical .f64, .f64 b => isCanonicalNaN64 b
  | .nanArithmetic .f64, .f64 b => isArithmeticNaN64 b
  | .anyRef .funcref, .ref (.func _) => true
  | .anyRef .externref, .ref (.extern _) => true
  | .anyNull, .ref (.null _) => true
  | _, _ => false

/-! ## Script state -/

abbrev HostState := Unit

/-- The store, the names imports resolve against, and the modules loaded so
far. A module that failed to load is remembered as `none` so later commands
are marked unavailable instead of failing. -/
structure ScriptState where
  dir : System.FilePath
  store : Store HostState
  registry : Link.Registry
  /-- Names registered for modules that did not load. -/
  unavailable : List String := []
  current : Option (Option ModuleInst) := none
  named : List (String × Option ModuleInst) := []

def ScriptState.init (dir : System.FilePath) : ScriptState :=
  let (store, spectest) := Link.allocateHost (Store.empty ()) Host.spectest
  { dir, store, registry := [("spectest", spectest)] }

def ScriptState.lookup (s : ScriptState) (name? : Option String) : Option (Option ModuleInst) :=
  match name? with
  | some n => (s.named.find? (·.1 == n)).map (·.2)
  | none => s.current

def limits : ExecLimits := {}
def fuel : Nat := 2_000_000_000

def loadModule (s : ScriptState) (filename : String) : IO (Except Binary.DecodeError Module) := do
  let bytes ← IO.FS.readBinFile (s.dir / filename)
  return Binary.decode bytes

/-- Decode and validate a module the suite expects to be valid. -/
def loadValid (s : ScriptState) (filename : String) : IO (Except Outcome ValidModule) := do
  match ← loadModule s filename with
  | .error (.unsupported _ feature) => return .error (.outOfScope feature)
  | .error e => return .error (.decodeError e.message)
  | .ok m =>
    match m.validate .all with
    | .ok vm => return .ok vm
    | .error (.unsupported feature) => return .error (.outOfScope feature)
    | .error e => return .error (.invalidError e.message)

/-- Record the result of a `module` command. -/
def ScriptState.loaded (s : ScriptState) (name? : Option String) (inst : Option ModuleInst) :
    ScriptState :=
  let named := match name? with | some n => (n, inst) :: s.named | none => s.named
  { s with current := some inst, named }

/-- Run an action (`invoke` or `get`) and return its values. -/
def runAction (s : ScriptState) (action : Json) :
    IO (Except String (Except Trap (List Value) × ScriptState)) := do
  let some inst := s.lookup (str? action "module") | return .error "unavailable"
  let some inst := inst | return .error "unavailable"
  let some field := str? action "field" | return .error "action without field"
  match str? action "type" with
  | some "invoke" =>
    let args ← match (arr action "args").toList.mapM parseValue with
      | .ok a => pure a
      | .error e => return .error e
    match inst.export? field with
    | some (.func addr) =>
      match Exec.invoke s.store limits fuel addr args with
      | .done values store => return .ok (.ok values, { s with store })
      | .trap reason store => return .ok (.error reason, { s with store })
      | .outOfFuel _ => return .error "out of fuel"
    | _ => return .error s!"no function export {field}"
  | some "get" =>
    match inst.export? field with
    | some (.global addr) =>
      match s.store.globals[addr]? with
      | some g => return .ok (.ok [g.value], s)
      | none => return .error "dangling global"
    | _ => return .error s!"no global export {field}"
  | _ => return .error "unknown action type"

/-- Run one command, returning its outcome and the updated state. -/
def runCommand (s : ScriptState) (cmd : Json) : IO (Outcome × ScriptState) := do
  let kind := (str? cmd "type").getD "?"
  let moduleType := (str? cmd "module_type").getD "binary"
  let text := (str? cmd "text").getD ""
  match kind with
  | "module" =>
    let some filename := str? cmd "filename" | return (.fail "module without filename", s)
    let name? := str? cmd "name"
    if moduleType != "binary" then return (.outOfScope "text", s.loaded name? none)
    match ← loadValid s filename with
    | .error outcome => return (outcome, s.loaded name? none)
    | .ok vm =>
      match Link.instantiateWith s.store limits s.registry vm with
      | .ok (store, inst) => return (.pass, { s with store }.loaded name? (some inst))
      | .error (.unknownImport m n) =>
        if s.unavailable.contains m then return (.moduleUnavailable, s.loaded name? none)
        else return (.fail s!"unknown import {m}.{n}", s.loaded name? none)
      | .error e => return (.fail s!"instantiation failed: {e.message}", s.loaded name? none)
  | "register" =>
    let some as := str? cmd "as" | return (.fail "register without name", s)
    match s.lookup (str? cmd "name") with
    | some (some inst) => return (.pass, { s with registry := (as, inst) :: s.registry })
    | _ => return (.moduleUnavailable, { s with unavailable := as :: s.unavailable })
  | "assert_malformed" =>
    let some filename := str? cmd "filename" | return (.fail "assert without filename", s)
    if moduleType != "binary" then return (.outOfScope "text", s)
    match ← loadModule s filename with
    | .ok _ => return (.fail s!"accepted a malformed module ({text})", s)
    | .error _ => return (.pass, s)
  | "assert_invalid" =>
    let some filename := str? cmd "filename" | return (.fail "assert without filename", s)
    if moduleType != "binary" then return (.outOfScope "text", s)
    match ← loadModule s filename with
    | .error (.unsupported _ feature) => return (.outOfScope feature, s)
    | .error e => return (.decodeError s!"assert_invalid module: {e.message}", s)
    | .ok m =>
      match m.validate .all with
      | .ok _ => return (.fail s!"accepted an invalid module ({text})", s)
      | .error (.unsupported feature) => return (.outOfScope feature, s)
      | .error _ => return (.pass, s)
  | "assert_unlinkable" | "assert_uninstantiable" =>
    let some filename := str? cmd "filename" | return (.fail "assert without filename", s)
    if moduleType != "binary" then return (.outOfScope "text", s)
    match ← loadValid s filename with
    | .error outcome => return (outcome, s)
    | .ok vm =>
      match Link.instantiateWith s.store limits s.registry vm, kind with
      | .ok _, _ => return (.fail s!"instantiated a module expected to fail ({text})", s)
      | .error (.trap reason store), "assert_uninstantiable" =>
        if text.startsWith reason.message then return (.pass, { s with store })
        else return (.fail s!"trapped with {reason.message}, expected {text}", { s with store })
      | .error (.trap reason store), _ =>
        return (.fail s!"trapped with {reason.message}, expected a link error: {text}",
          { s with store })
      | .error (.internal m), _ => return (.fail s!"internal: {m}", s)
      | .error (.unknownImport m _), _ =>
        if s.unavailable.contains m then return (.moduleUnavailable, s)
        else if kind == "assert_unlinkable" then return (.pass, s)
        else return (.fail s!"unknown import {m}, expected a trap: {text}", s)
      | .error _, "assert_unlinkable" => return (.pass, s)
      | .error e, _ => return (.fail s!"link error, expected a trap: {e.message}", s)
  | "assert_return" | "assert_trap" | "assert_exhaustion" | "action" =>
    let action := (cmd.getObjVal? "action").toOption.getD Json.null
    match s.lookup (str? action "module") with
    | some none => return (.moduleUnavailable, s)
    | none => return (.fail "no module to act on", s)
    | some (some _) =>
      match ← runAction s action with
      | .error e => return (.fail e, s)
      | .ok (result, s) =>
        match kind, result with
        | "assert_return", .ok values =>
          match (arr cmd "expected").toList.mapM parseExpected with
          | .error "unsupported" => return (.outOfScope "gc", s)
          | .error e => return (.fail e, s)
          | .ok expected =>
            let ok := expected.length == values.length &&
              (expected.zip values).all (fun (e, v) => matchesExpected e v)
            if ok then return (.pass, s) else return (.fail s!"got {repr values}", s)
        | "assert_return", .error t => return (.fail s!"trapped: {t.message}", s)
        | "action", .ok _ => return (.pass, s)
        | "action", .error t => return (.fail s!"trapped: {t.message}", s)
        | _, .ok values => return (.fail s!"expected a trap ({text}), got {repr values}", s)
        | _, .error t =>
          -- The reference interpreter appends detail to some messages
          -- ("uninitialized element 2").
          if text.startsWith t.message then return (.pass, s)
          else return (.fail s!"trapped with {t.message}, expected {text}", s)
  | "assert_exception" => return (.outOfScope "exceptions", s)
  | "module_definition" | "module_instance" => return (.outOfScope "module-instances", s)
  | _ => return (.skipped kind, s)

/-- Files that exercise a feature outside our scope as a whole, with the
feature: every command in them is reported `out_of_scope` without running.
Read from `testsuite_out_of_scope.txt` in the working directory, one
`file feature` pair per line. -/
def outOfScopeFiles : IO (List (String × String)) := do
  let path : System.FilePath := "testsuite_out_of_scope.txt"
  unless ← path.pathExists do return []
  let text ← IO.FS.readFile path
  return text.splitOn "\n" |>.filterMap fun line =>
    match (line.splitOn " ").filter (· != "") with
    | [file, feature] => some (file, feature)
    | _ => none

/-- Run a `.wast` file through `wasm-tools json-from-wast` into `scratch`,
then execute every command. -/
def runFile (scratch : System.FilePath) (outOfScope : List (String × String)) (path : String) :
    IO FileResult := do
  let stem := ((System.FilePath.mk path).fileStem).getD "script"
  let dir := scratch / stem
  IO.FS.createDirAll dir
  let json := dir / "script.json"
  let out ← IO.Process.output {
    cmd := "wasm-tools",
    args := #["json-from-wast", path, "--wasm-dir", dir.toString, "-o", json.toString] }
  if out.exitCode != 0 then
    return { path, fileError := some s!"wasm-tools failed: {out.stderr.trimAsciiEnd}" }
  let text ← IO.FS.readFile json
  let script ← match Json.parse text with
    | .ok j => pure j
    | .error e => return { path, fileError := some s!"bad JSON: {e}" }
  let commands := arr script "commands"
  let fileName := (System.FilePath.mk path).fileName.getD path
  if let some (_, feature) := outOfScope.find? (·.1 == fileName) then
    return { path, results := commands.map fun cmd =>
      { line := (nat? cmd "line").getD 0, kind := (str? cmd "type").getD "?",
        outcome := .outOfScope feature } }
  let mut state : ScriptState := .init dir
  let mut results : Array CmdResult := #[]
  for cmd in commands do
    let (outcome, state') ← runCommand state cmd
    state := state'
    results := results.push {
      line := (nat? cmd "line").getD 0, kind := (str? cmd "type").getD "?", outcome }
  return { path, results }

end Wasm.Testsuite
