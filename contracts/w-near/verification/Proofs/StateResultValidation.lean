import Harness.Main
import Proofs.RegisterHostValidation
import Proofs.StateReadResultSteps

/-! Captured exact sequential state-result copies on the accepted present-tag branch. -/
namespace WNear.Proofs.StateResultValidation
open Wasm Wasm.Near WNear.Testing MeteredLogic

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [498]
  let mut checked := 0
  let mut outside := 0
  let mut getter := 0
  for (method, entry) in seen.getD 498 #[] do
    let out := UInt32.ofNat (u32Arg entry.args 0)
    let source := UInt32.ofNat (u32Arg entry.args 1)
    let memory := h.mem entry.store
    if readI32 memory source.toNat == 0 then
      outside := outside + 1
      continue
    let result := h.call entry.store 498 entry.args
    match result.ending with
    | .returned [] => pure ()
    | _ => throw (IO.userError "state result copy failed")
    let expected := StateReadResult.finalMemory memory out source
    if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
      throw (IO.userError "state result sequential memory mismatch")
    if result.gas != op h 26 then throw (IO.userError s!"state result exact gas mismatch: {result.gas}")
    RegisterHostValidation.fuelBoundary h 498 17 entry
    if h.stackPointer result.after != h.stackPointer entry.store ||
        result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
        result.after.host.returnData != entry.store.host.returnData ||
        result.after.host.returnedPromise != entry.store.host.returnedPromise then
      throw (IO.userError "state result host/SP frame mismatch")
    if method == "ft_total_supply" then getter := getter + 1
    checked := checked + 1
  if checked == 0 || getter == 0 then throw (IO.userError "missing accepted state result/getter captures")
  IO.println s!"PASS state result f498: {checked} accepted captures ({getter} getter), {outside} outside; exact sequential memory/gas/fuel and host/SP"
#eval validate
end WNear.Proofs.StateResultValidation
