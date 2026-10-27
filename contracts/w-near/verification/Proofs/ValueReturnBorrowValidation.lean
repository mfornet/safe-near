import Harness.Main

/-! Captured normal-branch validation for f429/f430/f431/f433 and their actual
counter helpers f494/f672. Run from contracts/w-near/verification:
    lake env lean Proofs/ValueReturnBorrowValidation.lean
These are executable checks, not semantic proofs. -/
namespace WNear.Proofs.ValueReturnBorrowValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok module => pure module
    | .error error => throw (IO.userError error.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [429, 430, 431, 433, 494, 672]
  for (index, units) in [(429, 71), (430, 12), (431, 35), (433, 21), (494, 39), (672, 17)] do
    let captures := seen.getD index #[]
    if captures.isEmpty then throw (IO.userError s!"no captures for f{index}")
    for (method, entry) in captures do
      let result := h.call entry.store index entry.args
      if result.gas != op h units then
        throw (IO.userError s!"f{index} gas {result.gas / h.cfg.wasm.regularOpCost}, expected {units}")
      match result.ending with
      | .returned values =>
        match index with
        | 430 =>
          if returnsU32 result != some (u32Arg entry.args 0) then throw (IO.userError "f430 pointer mismatch")
        | 672 =>
          let address := u32Arg entry.args 0
          if returnsU32 result != some (h.readNat entry.store address 4) ||
              h.readNat result.after address 4 != u32Arg entry.args 1 then
            throw (IO.userError "f672 swap mismatch")
        | 494 =>
          let address := u32Arg entry.args 0
          if returnsU32 result != some address ||
              h.readNat result.after address 4 != (h.readNat entry.store address 4 + 1) % 2 ^ 32 then
            throw (IO.userError "f494 increment mismatch")
        | 431 =>
          let address := h.readNat entry.store (u32Arg entry.args 0) 4
          if !values.isEmpty || h.readNat result.after address 4 !=
              (h.readNat entry.store address 4 + 2 ^ 32 - 1) % 2 ^ 32 then
            throw (IO.userError "f431 decrement mismatch")
        | 429 =>
          let out := u32Arg entry.args 0
          let cell := u32Arg entry.args 1
          if !values.isEmpty || h.readNat result.after out 4 != (cell + 4) % 2 ^ 32 ||
              h.readNat result.after (out + 4) 4 != cell then
            throw (IO.userError "f429 borrow record mismatch")
        | _ =>
          if !values.isEmpty then throw (IO.userError s!"f{index} not void")
      | other => throw (IO.userError s!"f{index} failed: {other.describe}")
      if index == 430 || index == 433 then
        if !(changedBytes (h.mem entry.store) (h.mem result.after)).isEmpty then
          throw (IO.userError s!"f{index} normal path wrote memory")
      if method == "ft_total_supply" then IO.println s!"f{index} actual totalSupply normal call: units={units}"
    IO.println s!"PASS f{index}: {captures.size} captures, exact {units} units and normal effects"
  for sp in [0, 1, 15, 16, 2 ^ 32 - 1] do
    let store := h.setGlobal h.store 0 (i32 sp)
    let result := h.call store 433 [i32 0]
    if result.gas != op h 21 || h.stackPointer result.after != sp then
      throw (IO.userError "f433 wrapping stack-pointer fixture failed")
    match result.ending with
    | .returned [] => pure ()
    | _ => throw (IO.userError "f433 zero fixture did not return")
  for ptr in [1, 16, 2 ^ 32 - 1] do
    let result := h.call h.store 430 [i32 ptr, i32 (2 ^ 32 - 1)]
    if result.gas != op h 12 || returnsU32 result != some ptr then
      throw (IO.userError "f430 nonzero-pointer fixture failed")
  IO.println "PASS f430/f433: 8 pointer/wrapping-SP border fixtures"

#eval validate

end WNear.Proofs.ValueReturnBorrowValidation
