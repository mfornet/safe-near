import Harness.Main
import NearVM.MeteredHosts.RegisterReadMemory

/-! Captured deployed register forwarders: exact fees, memory, results and fuel boundaries. -/
namespace WNear.Proofs.RegisterHostValidation
open Wasm Wasm.Near WNear.Testing

def fuelBoundary (h : Harness) (index fuel : Nat) (entry : Entry) : IO Unit := do
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
  let seen ← captureAll protocol module bytes.size [240,241]
  for index in [240,241] do
    let mut checked := 0
    let mut getter := 0
    for (method, entry) in seen.getD index #[] do
      let register := UInt64.ofNat (u64Arg entry.args 1)
      let ptr := UInt64.ofNat (u64Arg entry.args 2)
      let original := h.mem entry.store
      let hostView : HostStore NearState := ⟨original, entry.store.host⟩
      let some data := entry.store.host.registers register.toNat
        | throw (IO.userError s!"unexpected absent register at f{index}")
      let result := h.call entry.store index entry.args
      let expected := if index == 240 then original.writeList ptr.toNat data else original
      let values := if index == 240 then [] else [Value.i64 (MeteredHosts.RegisterRead.lengthValue hostView register)]
      match result.ending with
      | .returned actual =>
        if actual != values then throw (IO.userError s!"f{index} result mismatch")
      | _ => throw (IO.userError s!"f{index} did not return")
      if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
        throw (IO.userError s!"f{index} exact memory mismatch")
      let cost := if index == 240 then MeteredHosts.RegisterRead.readCost entry.store.host data.length
        else entry.store.host.extCosts.cost "base"
      let units := if index == 240 then 14 else 12
      if result.gas != op h units + cost then throw (IO.userError s!"f{index} exact gas mismatch actual={result.gas} expected={op h units + cost} op={h.cfg.wasm.regularOpCost} host={cost}")
      fuelBoundary h index (if index == 240 then 4 else 3) entry
      if h.stackPointer result.after != h.stackPointer entry.store ||
          result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
          result.after.host.returnData != entry.store.host.returnData ||
          result.after.host.returnedPromise != entry.store.host.returnedPromise then
        throw (IO.userError s!"f{index} SP/host frame mismatch")
      if method == "ft_total_supply" then getter := getter + 1
      checked := checked + 1
    if checked == 0 || getter == 0 then throw (IO.userError s!"missing getter register capture f{index}")
    IO.println s!"PASS register forwarder f{index}: {checked} captures, {getter} getter; exact result/memory/gas/fuel and host/SP"
#eval validate
end WNear.Proofs.RegisterHostValidation
