import Harness.Main
import NearVM.MeteredStorageReadRules
import Proofs.RegisterHostValidation

/-! Captured storage-read inputs replayed with fresh canonical accounting at both node-billing modes. -/
namespace WNear.Proofs.StorageReadHostValidation
open Wasm Wasm.Near WNear.Testing MeteredHosts
open _root_.Near.TrieOverlay

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [284]
  let mut hits := 0
  let mut misses := 0
  let mut getter := 0
  for (method, captured) in seen.getD 284 #[] do
    for accountNodes in [false,true] do
      for absent in [false,true] do
        let keyLen := UInt64.ofNat (u64Arg captured.args 1)
        let keyPtr := UInt64.ofNat (u64Arg captured.args 2)
        let register := UInt64.ofNat (u64Arg captured.args 3)
        let source := if absent then { captured.store with host := { captured.store.host with
          storage := fun _ => none, storageKeys := [] } } else captured.store
        let entries := source.host.storageKeys.filterMap fun key =>
          (source.host.storage key).map fun value =>
            (contractKey source.host.context.currentAccountId key,value)
        let initial ← orThrow (Near.TrieOverlay.start entries)
        let entry := { captured with store := { source with host := { source.host with
          storageAccounting := some initial, storageReadsFromTrie := accountNodes } } }
        let original : HostStore NearState := ⟨h.mem entry.store, entry.store.host⟩
        let some key := getMemOrReg original keyPtr keyLen
          | throw (IO.userError "storage key span invalid")
        let plan := StorageRead.readPlan initial (contractKey original.host.context.currentAccountId key)
          original.host.storageReadsFromTrie
        let value := original.host.storage key
        let fee := burnSum original.host.extCosts (StorageRead.preCharges original keyLen keyPtr register) +
          burnSum original.host.extCosts (plan.charges initial) +
          (match value with | none => 0 | some data => burnSum original.host.extCosts (writeReg data.length))
        let result := h.call entry.store 284 entry.args
        let expected := if value.isSome then (1 : UInt64) else 0
        match result.ending with
        | .returned [.i64 actual] =>
          if actual != expected then throw (IO.userError "storage forwarder result mismatch")
        | _ => throw (IO.userError "storage forwarder did not return i64")
        if (h.mem result.after).pages != original.mem.pages || (h.mem result.after).max != original.mem.max then
          throw (IO.userError "storage forwarder memory frame mismatch")
        let expectedRegister := if register == u64Max || value.isNone then original.host.registers register.toNat else value
        if result.after.host.registers register.toNat != expectedRegister then
          throw (IO.userError "storage forwarder register write mismatch")
        if result.gas != op h 16 + fee then
          throw (IO.userError s!"storage forwarder gas mismatch actual={result.gas} expected={op h 16 + fee}")
        RegisterHostValidation.fuelBoundary h 284 5 entry
        if h.stackPointer result.after != h.stackPointer entry.store ||
            result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
            result.after.host.returnData != entry.store.host.returnData ||
            result.after.host.returnedPromise != entry.store.host.returnedPromise then
          throw (IO.userError "storage forwarder SP/host frame mismatch")
        if value.isSome then hits := hits + 1 else misses := misses + 1
        if method == "ft_total_supply" then getter := getter + 1
  if hits == 0 || misses == 0 || getter == 0 then throw (IO.userError "missing storage forwarder hit/miss/getter captures")
  IO.println s!"PASS canonical storage forwarder replay f284: {hits} hits/{misses} misses, {getter} getter; both node modes plus explicit absence fixtures; pure-plan exact gas, result/register/memory and fuel"
#eval validate
end WNear.Proofs.StorageReadHostValidation
