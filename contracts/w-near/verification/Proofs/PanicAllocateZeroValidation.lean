import Harness.Main

/-! Reproduce zero-size allocation captures: `lake env lean Proofs/PanicAllocateZeroValidation.lean`. -/
namespace WNear.Proofs.PanicAllocateZeroValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok module => pure module
    | .error error => throw (IO.userError error.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [509]
  let captures := seen.getD 509 #[]
  let mut accepted := 0
  for (_, entry) in captures do
    if u32Arg entry.args 1 != 0 then continue
    let out := u32Arg entry.args 0
    let alignment := u32Arg entry.args 2
    let result := h.call entry.store 509 entry.args
    match result.ending with
    | .returned [] => pure ()
    | ending => throw (IO.userError s!"f509 zero-size failure: {ending.describe}")
    if result.gas != op h 21 || h.readNat result.after out 4 != alignment || h.readNat result.after (out + 4) 4 != 0 then
      throw (IO.userError "f509 zero-size gas/record mismatch")
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[509]! entry.args
      | throw (IO.userError "cannot start f509")
    match (runInitialized h.cfg.wasm 15 (.next initial)).1 with
    | .done [] _ => pure ()
    | _ => throw (IO.userError "f509 zero-size did not return at fuel15")
    match (runInitialized h.cfg.wasm 14 (.next initial)).2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError "f509 zero-size fuel boundary mismatch")
    accepted := accepted + 1
  if accepted == 0 then throw (IO.userError "no captured zero-size f509 inputs")
  IO.println s!"PASS f509 zero-size: {accepted}/{captures.size} captures, exact21units/15steps, alignment/zero record"

#eval validate
end WNear.Proofs.PanicAllocateZeroValidation
