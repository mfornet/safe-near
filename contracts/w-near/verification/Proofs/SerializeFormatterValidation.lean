import Harness.Main

/-! Captured exact scalar prefixes of the actual U128 formatting adapters. -/
namespace WNear.Proofs.SerializeFormatterValidation
open Wasm Wasm.Near WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [353,901]
  for (index, steps, units, target) in [(353,3,12,901),(901,8,17,902)] do
    let mut checked := 0
    for (method, entry) in seen.getD index #[] do
      if method != "ft_total_supply" then continue
      let pointer := u32Arg entry.args 0
      let context := UInt32.ofNat (u32Arg entry.args 1)
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
        | throw (IO.userError s!"cannot start f{index}")
      let result := runInitialized h.cfg.wasm steps (.next initial)
      let .next current := result.1 | throw (IO.userError s!"f{index} prefix stopped unexpectedly")
      let callTarget := match current.nextInstr? with | some (.call n) => some n | _ => none
      if result.2 != some (.executionIssue .fuelExhausted) || callTarget != some target then
        throw (IO.userError s!"f{index} prefix did not reach exact next call")
      let expected : List Value := if index == 353 then
        [.i32 (UInt32.ofNat (h.readNat entry.store pointer 4)), .i32 context]
        else [.i64 (UInt64.ofNat (h.readNat entry.store pointer 8)),
          .i64 (UInt64.ofNat (h.readNat entry.store (pointer+8) 8)), .i32 1, .i32 context]
      if current.thread.stack.toList != expected then throw (IO.userError s!"f{index} exact argument stack mismatch")
      if current.store.host.gas.burnt-entry.store.host.gas.burnt != op h units then
        throw (IO.userError s!"f{index} prefix gas mismatch")
      if (h.mem current.store).pages != (h.mem entry.store).pages || h.stackPointer current.store != h.stackPointer entry.store then
        throw (IO.userError s!"f{index} prefix memory/SP mismatch")
      checked := checked+1
    if checked == 0 then throw (IO.userError s!"no getter prefix f{index}")
    IO.println s!"PASS getter f{index}: exact{steps}-step scalar prefix/{units} root gas; real f{target} arguments"
#eval validate
end WNear.Proofs.SerializeFormatterValidation
