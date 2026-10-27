import Harness.Main

/-! Exact captured checks for first panic-hook setup and its zero-size allocation
path. Separate from the integrated nine-contract harness and kernel proofs.
Run: lake env lean Proofs/PanicHookValidation.lean -/
namespace WNear.Proofs.PanicHookValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow (Wasm.Binary.decode bytes |>.mapError (·.message))
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [503, 508, 509, 522, 822]
  for (index, units, fuel) in [(503, 85, 62), (508, 55, 40), (509, 21, 15), (522, 139, 103), (822, 41, 35)] do
    let captures := seen.getD index #[]
    let mut checked := 0
    let mut outside := 0
    for (_, entry) in captures do
      let zero := if index == 503 then u32Arg entry.args 0 == 0 else
        if index == 508 || index == 509 then u32Arg entry.args 1 == 0 else true
      let first := if index == 522 || index == 822 then
        h.readNat entry.store 1074932 4 == 0 && h.readNat entry.store 1074920 4 == 0 && h.readNat entry.store 1074928 4 == 0
        else true
      if !zero || !first then
        outside := outside + 1
        continue
      let result := h.call entry.store index entry.args
      if result.gas != op h units then throw (IO.userError s!"f{index} exact gas mismatch")
      if index == 503 then
        if returnsU32 result != some (u32Arg entry.args 1) then throw (IO.userError "f503 zero-size pointer mismatch")
      else
        match result.ending with
        | .returned [] => pure ()
        | _ => throw (IO.userError s!"f{index} did not return void")
      if index == 508 || index == 509 then
        let out := u32Arg entry.args 0
        if h.readNat result.after out 4 != u32Arg entry.args 2 || h.readNat result.after (out + 4) 4 != 0 then
          throw (IO.userError s!"f{index} zero-size result record mismatch")
      if index == 522 || index == 822 then
        let receiver := if index == 522 then 1 else u32Arg entry.args 0
        let vtable := if index == 522 then 1055136 else u32Arg entry.args 1
        if h.readNat result.after 1074924 4 != receiver || h.readNat result.after 1074928 4 != vtable ||
            h.readNat result.after 1074920 4 != 0 || h.readNat result.after 1074932 4 != 0 then
          throw (IO.userError s!"f{index} installed-hook/lock/flag mismatch")
      if h.stackPointer result.after != h.stackPointer entry.store ||
          result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
          result.after.host.returnData != entry.store.host.returnData ||
          result.after.host.returnedPromise != entry.store.host.returnedPromise then
        throw (IO.userError s!"f{index} SP/host-frame mismatch")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
        | throw (IO.userError s!"cannot start f{index}")
      match (runInitialized h.cfg.wasm fuel (.next initial)).1 with
      | .done _ _ => pure ()
      | _ => throw (IO.userError s!"f{index} exact fuel mismatch")
      match (runInitialized h.cfg.wasm (fuel - 1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError s!"f{index} one-less-fuel mismatch")
      checked := checked + 1
    if checked == 0 then throw (IO.userError s!"no accepted f{index} captures")
    IO.println s!"PASS f{index}: {checked} accepted captures; exact {units} units/{fuel} steps; {outside} captures outside contract"
#eval validate
end WNear.Proofs.PanicHookValidation
