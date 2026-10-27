import Harness.Main
import NearVM.MeteredI32MemoryRules

/-! Reproducible captured checks before proving serializer helpers. -/
namespace WNear.Proofs.SerializeValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

def checkFuel (h : Harness) (index fuel : Nat) (entry : Entry) : IO Unit := do
  let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
    | throw (IO.userError s!"cannot start f{index}")
  match (runInitialized h.cfg.wasm fuel (.next initial)).1 with
  | .done _ _ => pure ()
  | _ => throw (IO.userError s!"f{index} exact fuel mismatch")
  match (runInitialized h.cfg.wasm (fuel - 1) (.next initial)).2 with
  | some (.executionIssue .fuelExhausted) => pure ()
  | _ => throw (IO.userError s!"f{index} one-less-fuel mismatch")

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [472,365,321]
  for index in [472,365,321] do
    let mut checked := 0
    let mut getter := 0
    for (method, entry) in seen.getD index #[] do
      let a := UInt32.ofNat (u32Arg entry.args 0)
      if index == 365 && a != 0 then continue
      let result := h.call entry.store index entry.args
      match result.ending with
      | .returned [] => pure ()
      | _ => throw (IO.userError s!"f{index} did not return void")
      let original := h.mem entry.store
      let expected := if index == 472 then
        writeI32 (writeI32 original (a.toNat+4) (UInt32.ofNat (u32Arg entry.args 2))) a.toNat (UInt32.ofNat (u32Arg entry.args 1))
        else if index == 365 then original else h.mem (h.call entry.store 68 entry.args).after
      if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
        throw (IO.userError s!"f{index} exact sequential memory mismatch")
      if index == 472 || index == 365 then
        let units := if index == 472 then 16 else 21
        let fuel := if index == 472 then 7 else 14
        if result.gas != op h units then throw (IO.userError s!"f{index} exact gas mismatch")
        checkFuel h index fuel entry
      else
        let reference := h.call entry.store 68 entry.args
        if result.gas != reference.gas then throw (IO.userError "f321/f68 gas mismatch")
      if h.stackPointer result.after != h.stackPointer entry.store ||
          result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
          result.after.host.returnData != entry.store.host.returnData ||
          result.after.host.returnedPromise != entry.store.host.returnedPromise then
        throw (IO.userError s!"f{index} SP/host frame mismatch")
      if method == "ft_total_supply" then getter := getter + 1
      checked := checked + 1
    if checked == 0 || getter == 0 then throw (IO.userError s!"missing accepted getter capture f{index}")
    IO.println s!"PASS serializer f{index}: {checked} accepted captures, {getter} getter; memory/SP/host and gas checked"
#eval validate
end WNear.Proofs.SerializeValidation
