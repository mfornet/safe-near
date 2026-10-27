import Harness.Main

/-! Reproduce the actual exclusive-borrow normal-path checks from the captured
campaign: `lake env lean Proofs/InterfaceBorrowValidation.lean`. -/
namespace WNear.Proofs.InterfaceBorrowValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok module => pure module
    | .error error => throw (IO.userError error.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [441, 442, 492]
  for (index, units) in [(441, 70), (442, 35), (492, 38)] do
    let captures := seen.getD index #[]
    if captures.isEmpty then throw (IO.userError s!"no captures for f{index}")
    let mut accepted := 0
    for (_, entry) in captures do
      let cell := if index == 441 then u32Arg entry.args 1 else u32Arg entry.args 0
      if index != 442 && h.readNat entry.store cell 4 != 0 then continue
      let result := h.call entry.store index entry.args
      if result.gas != op h units then throw (IO.userError s!"f{index} gas {result.gas / h.cfg.wasm.regularOpCost}, expected {units}")
      match result.ending with
      | .returned values =>
        if index == 492 then
          if returnsU32 result != some cell || h.readNat result.after cell 4 != 2 ^ 32 - 1 then
            throw (IO.userError "f492 exclusive acquisition mismatch")
        else if index == 441 then
          let out := u32Arg entry.args 0
          if !values.isEmpty || h.readNat result.after out 4 != (cell + 4) % 2 ^ 32 ||
              h.readNat result.after (out + 4) 4 != cell then throw (IO.userError "f441 record mismatch")
        else
          let counter := h.readNat entry.store cell 4
          if !values.isEmpty || h.readNat result.after counter 4 != (h.readNat entry.store counter 4 + 1) % 2 ^ 32 then
            throw (IO.userError "f442 release mismatch")
      | other => throw (IO.userError s!"f{index} did not return: {other.describe}")
      accepted := accepted + 1
    if accepted == 0 then throw (IO.userError s!"no accepted captures for f{index}")
    IO.println s!"PASS f{index}: {accepted}/{captures.size} normal captures, exact {units} units"

#eval validate
end WNear.Proofs.InterfaceBorrowValidation
