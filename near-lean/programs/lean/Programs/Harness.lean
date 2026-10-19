import Interpreter.Wasm.Host.Universal

/-! Reusable byte-stream harness for compiled Wasm test programs. -/

namespace Programs.Harness

open Wasm

inductive Failure where
  | missingExport (name : String)
  | unsupportedImports
  | initializationError (message : String)
  | trapped (reason : SmallStep.TrapReason)
  | outOfFuel
  | interpreterError (message : String)
  deriving Repr, BEq

/-- Execute a zero-argument export under the universal host. Resource limits,
traps, and interpreter errors remain distinct from successful empty output. -/
def run (m : Module) (op : String) (input : List UInt8) (fuel : Nat := 50_000_000) :
    Except Failure (List UInt8) := do
  let some entry := m.findExport op | throw (.missingExport op)
  unless Universal.covers m do
    throw .unsupportedImports
  let some signature := m.funcSig? entry
    | throw (.initializationError "export has no function signature")
  unless signature.params.isEmpty && signature.results.isEmpty do
    throw (.initializationError "stream programs require a () -> () export")
  let store : Store Universal.State :=
    { (m.initialStore (α := Universal.State)) with host := Universal.State.ofInput input }
  let config ←
    match SmallStep.initConfig { module := m, host := Universal.envFor m } entry store [] with
    | .error error =>
      .error (.initializationError error.message)
    | .ok config =>
      .ok config
  match (SmallStep.runSteps fuel config).result with
  | .success _ final =>
    return final.wasm.host.stdio.output
  | .trapped reason _ =>
    throw (.trapped reason)
  | .outOfFuel _ =>
    throw .outOfFuel
  | .internalError error _ =>
    throw (.interpreterError error.message)

/-- Compatibility adapter for callers that only need success or failure. -/
def runBytes (m : Module) (op : String) (input : List UInt8) (fuel : Nat := 50_000_000) :
    Option (List UInt8) :=
  (run m op input fuel).toOption

def le32 (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

def le64 (x : UInt64) : List UInt8 :=
  (List.range 8).map fun i => (x >>> (8 * i).toUInt64).toUInt8

end Programs.Harness
