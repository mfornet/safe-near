import Harness.Main

/-! Captured normal-path checks for the complete f456/f545 call chain.
Run: lake env lean Proofs/ValueReturnOuterValidation.lean -/
namespace WNear.Proofs.ValueReturnOuterValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok module => pure module
    | .error error => throw (IO.userError error.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [456, 545]
  for (index, units, fuel) in [(456, 247, 160), (545, 277, 181)] do
    let captures := seen.getD index #[]
    if captures.isEmpty then throw (IO.userError s!"no actual f{index} captures")
    for (method, entry) in captures do
      let slice := u32Arg entry.args 1
      let ptr := if index == 456 then h.readNat entry.store slice 4 else u32Arg entry.args 0
      let len := if index == 456 then h.readNat entry.store (slice + 4) 4 else u32Arg entry.args 1
      let result := h.call entry.store index entry.args
      match result.ending with
      | .returned [] => pure ()
      | ending => throw (IO.userError s!"f{index} did not return normally: {ending.describe}")
      let expectedBytes := h.read entry.store ptr len
      let fees := entry.store.host.fees.newDataReceiptByte
      let dataCost := (entry.store.host.outputDataReceivers.map fun receiver =>
        fees.send (receiver == entry.store.host.context.currentAccountId) * len + fees.execution * len).sum
      let expectedGas := op h units + entry.store.host.extCosts.cost "base" +
        entry.store.host.extCosts.cost "read_memory_base" + entry.store.host.extCosts.cost "read_memory_byte" * len + dataCost
      if result.gas != expectedGas || result.after.host.returnData != some expectedBytes then
        throw (IO.userError s!"f{index} bytes/gas mismatch: {method},gas={result.gas},expected={expectedGas}")
      if result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
          result.after.host.returnedPromise != none || h.stackPointer result.after != h.stackPointer entry.store then
        throw (IO.userError s!"f{index} storage-usage/promise/SP mismatch")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
        | throw (IO.userError s!"cannot start f{index}")
      match (runInitialized h.cfg.wasm fuel (.next initial)).1 with
      | .done [] _ => pure ()
      | _ => throw (IO.userError s!"f{index} did not return at exact fuel {fuel}")
      match (runInitialized h.cfg.wasm (fuel - 1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError s!"f{index} fuel boundary mismatch")
      if method == "ft_total_supply" then
        IO.println s!"f{index} actual totalSupply whole return: {units} units plus host fees / {fuel} steps, len={len}"
    IO.println s!"PASS f{index}: {captures.size} whole-path captures, exact bytes/gas/fuel, storage-usage/promise/SP"

#eval validate

end WNear.Proofs.ValueReturnOuterValidation
