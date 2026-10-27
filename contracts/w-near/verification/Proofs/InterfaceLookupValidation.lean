import Harness.Main

/-! Executable checks for the actual first-installation path. These captured
checks do not claim the still-open complete lazy-lookup/setter theorem.
Run: lake env lean Proofs/InterfaceLookupValidation.lean -/
namespace WNear.Proofs.InterfaceLookupValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow (Wasm.Binary.decode bytes |>.mapError (·.message))
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [463, 467, 468, 520, 565]
  for (index, units, fuel) in [(463, 314, 220), (467, 81, 64), (468, 99, 74),
      (520, 327, 225), (565, 110, 78)] do
    let mut checked := 0
    let mut initialized := 0
    for (_, entry) in seen.getD index #[] do
      if h.readNat entry.store 1074900 4 != 0 then
        initialized := initialized + 1
        continue
      let result := h.call entry.store index entry.args
      if result.gas != op h units then throw (IO.userError s!"f{index} lazy gas mismatch")
      if h.readNat result.after 1074900 4 != 1 || h.readNat result.after 1074904 4 != 0 then
        throw (IO.userError s!"f{index} status/borrow counter mismatch")
      if index == 463 || index == 520 then
        match result.ending with
        | .returned [] => pure ()
        | _ => throw (IO.userError s!"f{index} did not return void")
        let receiver := u32Arg entry.args (if index == 463 then 1 else 0)
        let vtable := u32Arg entry.args (if index == 463 then 2 else 1)
        if h.readNat result.after 1074908 4 != receiver || h.readNat result.after 1074912 4 != vtable then
          throw (IO.userError s!"f{index} installed receiver/vtable mismatch")
      else if returnsU32 result != some 1074904 then
        throw (IO.userError s!"f{index} lazy pointer mismatch")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
        | throw (IO.userError s!"cannot start f{index}")
      match (runInitialized h.cfg.wasm fuel (.next initial)).1 with
      | .done _ _ => pure ()
      | _ => throw (IO.userError s!"f{index} exact fuel mismatch")
      match (runInitialized h.cfg.wasm (fuel - 1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError s!"f{index} one-less fuel boundary mismatch")
      checked := checked + 1
    if checked == 0 then throw (IO.userError s!"no lazy f{index} captures")
    IO.println s!"PASS f{index}: {checked} lazy captures; exact {units} units/{fuel} steps; {initialized} initialized captures outside this suite"

#eval validate
end WNear.Proofs.InterfaceLookupValidation
