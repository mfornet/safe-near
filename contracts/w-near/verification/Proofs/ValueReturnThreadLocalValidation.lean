import Harness.Main

/-! Executable validation of the initialized branch of f468/f565.
Run: lake env lean Proofs/ValueReturnThreadLocalValidation.lean
Uninitialized captures are counted separately, not claimed by this contract. -/
namespace WNear.Proofs.ValueReturnThreadLocalValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok module => pure module
    | .error error => throw (IO.userError error.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [468, 565]
  for (index, units, fuel) in [(468, 17, 10), (565, 28, 14)] do
    let captures := seen.getD index #[]
    if captures.isEmpty then throw (IO.userError s!"no actual f{index} captures")
    let mut checked := 0
    let mut lazy := 0
    for (method, entry) in captures do
      let ptr := if index == 468 then u32Arg entry.args 0 else 1074900
      if h.readNat entry.store ptr 4 != 1 then
        lazy := lazy + 1
        continue
      let result := h.call entry.store index entry.args
      if result.gas != op h units || returnsU32 result != some ((ptr + 4) % 2 ^ 32) then
        throw (IO.userError s!"f{index} initialized result/gas mismatch")
      if !(changedBytes (h.mem entry.store) (h.mem result.after)).isEmpty then
        throw (IO.userError s!"f{index} initialized path changed memory")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
        | throw (IO.userError s!"cannot start actual f{index}")
      match (runInitialized h.cfg.wasm fuel (.next initial)).1 with
      | .done [.i32 actual] _ =>
        if actual.toNat != (ptr + 4) % 2 ^ 32 then throw (IO.userError "wrong typed return")
      | _ => throw (IO.userError s!"f{index} did not return in exactly {fuel} steps")
      match (runInitialized h.cfg.wasm (fuel - 1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError s!"f{index} fuel boundary mismatch")
      checked := checked + 1
      if method == "ft_total_supply" then
        IO.println s!"f{index} actual totalSupply initialized lookup: {units} units / {fuel} steps"
    if checked == 0 then throw (IO.userError s!"no initialized f{index} captures")
    IO.println s!"PASS f{index}: {checked} initialized captures, exact bytes/gas/fuel; {lazy} lazy captures outside contract"

#eval validate

end WNear.Proofs.ValueReturnThreadLocalValidation
