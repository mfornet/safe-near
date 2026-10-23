import Wasm
import Lean.Data.Json

/-!
# One `.wast` script, command by command

A script is a sequence of commands (define a module, register it under a
name, invoke an export and compare, assert that something is rejected). The
driver asks `wasm-tools json-from-wast` for the command list and one binary
per module, then folds the commands over a `Session`: the store, the names
imports resolve against, and the modules defined so far.

Each command gets a `Verdict`. `ok` and the three bug verdicts (`wrong`,
`undecodable`, `invalid`) are what the suite says; `outOfScope`,
`unimplemented` and `unavailable` are coverage information.
-/

namespace Wasm.Testsuite

open Lean (Json)

inductive Verdict where
  /-- The command behaved as the specification says. -/
  | ok
  /-- It ran, with the wrong result. -/
  | wrong (why : String)
  /-- A module the suite expects to decode did not, for a reason in scope. -/
  | undecodable (why : String)
  /-- A module the suite expects to validate did not, for a reason in scope. -/
  | invalid (why : String)
  /-- The module uses a feature outside scope. -/
  | outOfScope (feature : String)
  /-- A command kind the driver does not run. -/
  | unimplemented (kind : String)
  /-- The command needs a module that did not load. -/
  | unavailable
deriving Repr, Inhabited

namespace Verdict

/-- The tag in the coverage report; stable, since CI diffs the report. -/
def tag : Verdict → String
  | ok => "pass"
  | wrong _ => "fail"
  | undecodable _ => "decode_error"
  | invalid _ => "invalid_error"
  | outOfScope f => s!"out_of_scope:{f}"
  | unimplemented k => s!"skipped:{k}"
  | unavailable => "module_unavailable"

def isBug : Verdict → Bool
  | wrong _ | undecodable _ | invalid _ => true
  | _ => false

def explanation : Verdict → String
  | wrong w | undecodable w | invalid w => w
  | _ => ""

end Verdict

/-- One command's verdict, with where it came from. -/
structure Row where
  line : Nat
  kind : String
  verdict : Verdict
deriving Inhabited

/-- A whole script's rows, or why it could not run at all. -/
structure ScriptRun where
  script : String
  rows : Array Row := #[]
  broken : Option String := none

/-! ## Reading the JSON -/

def field? (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok v => v.getStr?.toOption
  | .error _ => none

def number? (j : Json) (key : String) : Option Nat :=
  match j.getObjVal? key with
  | .ok v => v.getNat?.toOption
  | .error _ => none

def items (j : Json) (key : String) : List Json :=
  match j.getObjVal? key with
  | .ok v => (v.getArr?.toOption.getD #[]).toList
  | .error _ => []

/-- A constant from the script: integers and float bit patterns are decimal
strings (possibly negative), references are `null` or an opaque number. -/
def constant (ty value : String) : Except String Value := do
  let bits (n : Nat) : Except String Nat :=
    match value.toInt? with
    | some i => .ok (i % ((2 : Int) ^ n)).toNat
    | none => .error s!"not a number: {value}"
  match ty with
  | "i32" => return .i32 (UInt32.ofNat (← bits 32))
  | "i64" => return .i64 (UInt64.ofNat (← bits 64))
  | "f32" => return .f32 (UInt32.ofNat (← bits 32))
  | "f64" => return .f64 (UInt64.ofNat (← bits 64))
  | "funcref" => if value == "null" then return .ref (.null .funcref) else .error "funcref value"
  | "externref" =>
    if value == "null" then return .ref (.null .externref)
    else return .ref (.extern (← bits 64))
  | _ => .error s!"value type {ty}"

def argument (j : Json) : Except String Value := do
  let some ty := field? j "type" | .error "argument without a type"
  let some value := field? j "value" | .error "argument without a value"
  constant ty value

/-- What a result must satisfy. -/
inductive Expectation where
  | exactly (v : Value)
  | canonicalNaN (t : NumType)
  | arithmeticNaN (t : NumType)
  | someRef (t : RefType)
  | someNull
  /-- A reference type outside scope. -/
  | foreign

def expectation (j : Json) : Except String Expectation := do
  let some ty := field? j "type" | .error "expectation without a type"
  let value := (field? j "value").getD ""
  match ty, value with
  | "f32", "nan:canonical" => return .canonicalNaN .f32
  | "f32", "nan:arithmetic" => return .arithmeticNaN .f32
  | "f64", "nan:canonical" => return .canonicalNaN .f64
  | "f64", "nan:arithmetic" => return .arithmeticNaN .f64
  | "refnull", _ => return .someNull
  | "funcref", "null" => return .exactly (.ref (.null .funcref))
  | "funcref", _ => return .someRef .funcref
  | "externref", "null" => return .exactly (.ref (.null .externref))
  | "externref", _ => return .exactly (← constant ty value)
  | "i32", _ | "i64", _ | "f32", _ | "f64", _ => return .exactly (← constant ty value)
  | _, _ => return .foreign

/-- A NaN with only the quiet bit set (either sign). -/
def quietNaN32 (b : UInt32) : Bool := b &&& 0x7FFFFFFF == 0x7FC00000
def quietNaN64 (b : UInt64) : Bool := b &&& 0x7FFFFFFFFFFFFFFF == 0x7FF8000000000000
/-- A NaN with the quiet bit set, any payload. -/
def anyQuietNaN32 (b : UInt32) : Bool := b &&& 0x7FC00000 == 0x7FC00000
def anyQuietNaN64 (b : UInt64) : Bool := b &&& 0x7FF8000000000000 == 0x7FF8000000000000

def Expectation.accepts : Expectation → Value → Bool
  | .exactly v, w => v == w
  | .canonicalNaN .f32, .f32 b => quietNaN32 b
  | .canonicalNaN .f64, .f64 b => quietNaN64 b
  | .arithmeticNaN .f32, .f32 b => anyQuietNaN32 b
  | .arithmeticNaN .f64, .f64 b => anyQuietNaN64 b
  | .someRef .funcref, .ref (.func _) => true
  | .someRef .externref, .ref (.extern _) => true
  | .someNull, .ref (.null _) => true
  | _, _ => false

/-! ## The session -/

/-- A loaded module, or the memory of one that failed to load. -/
abbrev Loaded := Option ModuleInst

structure Session where
  binaries : System.FilePath
  store : Store Unit
  names : Link.Registry
  /-- Registered names whose module did not load, so that imports of them
  are "unavailable" rather than failures. -/
  missingNames : List String := []
  latest : Option Loaded := none
  byName : List (String × Loaded) := []

def Session.start (binaries : System.FilePath) : Session :=
  let (store, spectest) := Link.allocateHost (Store.empty ()) Host.spectest
  { binaries, store, names := [("spectest", spectest)] }

def Session.module? (s : Session) (name : Option String) : Option Loaded :=
  match name with
  | some n => (s.byName.lookup n)
  | none => s.latest

def Session.remember (s : Session) (name : Option String) (loaded : Loaded) : Session :=
  { s with latest := some loaded,
           byName := match name with | some n => (n, loaded) :: s.byName | none => s.byName }

def limits : ExecLimits := {}
def budget : Nat := 2_000_000_000

/-- Decode a module's binary; `unsupported` becomes out of scope. -/
def decoded (s : Session) (file : String) : IO (Except Verdict Module) := do
  let bytes ← IO.FS.readBinFile (s.binaries / file)
  return match Binary.decode bytes with
    | .ok m => .ok m
    | .error (.unsupported _ feature) => .error (.outOfScope feature)
    | .error e => .error (.undecodable e.message)

/-- Decode and validate. -/
def valid (s : Session) (file : String) : IO (Except Verdict ValidModule) := do
  match ← decoded s file with
  | .error v => return .error v
  | .ok m =>
    return match m.validate .all with
      | .ok vm => .ok vm
      | .error (.unsupported feature) => .error (.outOfScope feature)
      | .error e => .error (.invalid e.message)

/-- The reference interpreter's trap text may carry detail after ours. -/
def trapMatches (expected : String) (t : Trap) : Bool := expected.startsWith t.message

/-- Perform an action: call an export, or read an exported global. -/
def act (s : Session) (action : Json) : Except String (Except Trap (List Value) × Session) := do
  let some loaded := s.module? (field? action "module") | .error "no such module"
  let some inst := loaded | .error "module unavailable"
  let some name := field? action "field" | .error "action without a field"
  match field? action "type", inst.export? name with
  | some "invoke", some (.func addr) =>
    let args ← (items action "args").mapM argument
    match Exec.invoke s.store limits budget addr args with
    | .done values store => return (.ok values, { s with store })
    | .trap t store => return (.error t, { s with store })
    | .outOfFuel _ => .error "step budget exhausted"
  | some "get", some (.global addr) =>
    match s.store.globals[addr]? with
    | some g => return (.ok [g.value], s)
    | none => .error "dangling global"
  | _, _ => .error s!"no export {name} of the right kind"

/-- A binary assertion's module, or the reason it cannot be judged. -/
def binaryOf (cmd : Json) : Except Verdict String :=
  if (field? cmd "module_type").getD "binary" != "binary" then .error (.outOfScope "text")
  else match field? cmd "filename" with
    | some f => .ok f
    | none => .error (.wrong "command without a module file")

/-- Instantiate, mapping an unknown import of an unavailable name to `unavailable`. -/
def instantiated (s : Session) (vm : ValidModule) :
    Except Verdict (Store Unit × ModuleInst) ⊕ (Trap × Store Unit) :=
  match Link.instantiateWith s.store limits s.names vm with
  | .ok result => .inl (.ok result)
  | .error (.trap t store) => .inr (t, store)
  | .error (.unknownImport m _) =>
    if s.missingNames.contains m then .inl (.error .unavailable)
    else .inl (.error (.wrong s!"unknown import from {m}"))
  | .error e => .inl (.error (.wrong e.message))

/-- Run one command. -/
def perform (s : Session) (cmd : Json) : IO (Verdict × Session) := do
  let kind := (field? cmd "type").getD "?"
  let text := (field? cmd "text").getD ""
  match kind with
  | "module" =>
    let name := field? cmd "name"
    match binaryOf cmd with
    | .error v => return (v, s.remember name none)
    | .ok file =>
      match ← valid s file with
      | .error v => return (v, s.remember name none)
      | .ok vm =>
        match instantiated s vm with
        | .inl (.ok (store, inst)) => return (.ok, { s with store }.remember name (some inst))
        | .inl (.error v) => return (v, s.remember name none)
        | .inr (t, _) => return (.wrong s!"instantiation trapped: {t.message}", s.remember name none)
  | "register" =>
    let some alias := field? cmd "as" | return (.wrong "register without a name", s)
    match s.module? (field? cmd "name") with
    | some (some inst) => return (.ok, { s with names := (alias, inst) :: s.names })
    | _ => return (.unavailable, { s with missingNames := alias :: s.missingNames })
  | "assert_malformed" =>
    match binaryOf cmd with
    | .error v => return (v, s)
    | .ok file =>
      return match ← decoded s file with
        | .ok _ => (.wrong s!"decoded a malformed module ({text})", s)
        | .error _ => (.ok, s)
  | "assert_invalid" =>
    match binaryOf cmd with
    | .error v => return (v, s)
    | .ok file =>
      match ← decoded s file with
      | .error (.outOfScope f) => return (.outOfScope f, s)
      | .error (.undecodable why) => return (.undecodable s!"invalid-module fixture: {why}", s)
      | .error v => return (v, s)
      | .ok m =>
        return match m.validate .all with
          | .ok _ => (.wrong s!"validated an invalid module ({text})", s)
          | .error (.unsupported f) => (.outOfScope f, s)
          | .error _ => (.ok, s)
  | "assert_unlinkable" =>
    match binaryOf cmd with
    | .error v => return (v, s)
    | .ok file =>
      match ← valid s file with
      | .error v => return (v, s)
      | .ok vm =>
        return match instantiated s vm with
          | .inl (.ok _) => (.wrong s!"linked a module expected not to link ({text})", s)
          | .inl (.error .unavailable) => (.unavailable, s)
          | .inl (.error _) => (.ok, s)
          | .inr (t, store) => (.wrong s!"trapped ({t.message}) instead of failing to link", { s with store })
  | "assert_uninstantiable" =>
    match binaryOf cmd with
    | .error v => return (v, s)
    | .ok file =>
      match ← valid s file with
      | .error v => return (v, s)
      | .ok vm =>
        return match instantiated s vm with
          | .inl (.ok _) => (.wrong s!"instantiated a module expected to trap ({text})", s)
          | .inl (.error .unavailable) => (.unavailable, s)
          | .inl (.error v) => (.wrong s!"link error instead of a trap: {v.explanation}", s)
          | .inr (t, store) =>
            if trapMatches text t then (.ok, { s with store })
            else (.wrong s!"trapped with {t.message}, expected {text}", { s with store })
  | "assert_return" | "assert_trap" | "assert_exhaustion" | "action" =>
    let action := (cmd.getObjVal? "action").toOption.getD Json.null
    match s.module? (field? action "module") with
    | some none => return (.unavailable, s)
    | none => return (.wrong "no module to act on", s)
    | some (some _) =>
      match act s action with
      | .error why => return (.wrong why, s)
      | .ok (.ok values, s) =>
        if kind == "action" then return (.ok, s)
        if kind != "assert_return" then return (.wrong s!"ran to completion, expected a trap ({text})", s)
        match (items cmd "expected").mapM expectation with
        | .error why => return (.wrong why, s)
        | .ok expected =>
          if expected.any (· matches .foreign) then return (.outOfScope "gc", s)
          let agree := expected.length == values.length &&
            (List.zip expected values).all fun (e, v) => e.accepts v
          return (if agree then .ok else .wrong s!"results {repr values}", s)
      | .ok (.error t, s) =>
        if kind == "assert_return" || kind == "action" then
          return (.wrong s!"trapped: {t.message}", s)
        return (if trapMatches text t then .ok else .wrong s!"trapped with {t.message}, expected {text}", s)
  | "assert_exception" => return (.outOfScope "exceptions", s)
  | "module_definition" | "module_instance" => return (.outOfScope "module-instances", s)
  | other => return (.unimplemented other, s)

/-! ## Whole scripts -/

/-- Scripts outside scope as a whole, with the feature: `testsuite_out_of_scope.txt`
in the working directory lists them, one `file feature` per line. -/
def outOfScopeScripts : IO (List (String × String)) := do
  let path : System.FilePath := "testsuite_out_of_scope.txt"
  if !(← path.pathExists) then return []
  let lines := (← IO.FS.lines path).toList
  return lines.filterMap fun line =>
    match (line.splitOn " ").filter (· != "") with
    | [file, feature] => some (file, feature)
    | _ => none

/-- Split a script with `wasm-tools`, then perform every command. -/
def runScript (scratch : System.FilePath) (excluded : List (String × String)) (path : String) :
    IO ScriptRun := do
  let name := (System.FilePath.mk path).fileName.getD path
  let dir := scratch / ((System.FilePath.mk path).fileStem.getD "script")
  IO.FS.createDirAll dir
  let manifest := dir / "commands.json"
  let split ← IO.Process.output
    { cmd := "wasm-tools",
      args := #["json-from-wast", path, "--wasm-dir", dir.toString, "-o", manifest.toString] }
  if split.exitCode != 0 then
    return { script := path, broken := some s!"wasm-tools: {split.stderr.trimAsciiEnd}" }
  let commands ← match Json.parse (← IO.FS.readFile manifest) with
    | .ok j => pure (items j "commands")
    | .error why => return { script := path, broken := some s!"manifest: {why}" }
  let row (cmd : Json) (v : Verdict) : Row :=
    { line := (number? cmd "line").getD 0, kind := (field? cmd "type").getD "?", verdict := v }
  if let some (_, feature) := excluded.find? (·.1 == name) then
    let rows := (commands.map fun cmd => row cmd (.outOfScope feature)).toArray
    return { script := path, rows }
  let mut session := Session.start dir
  let mut rows := #[]
  for cmd in commands do
    let (verdict, next) ← perform session cmd
    session := next
    rows := rows.push (row cmd verdict)
  return { script := path, rows }

end Wasm.Testsuite
