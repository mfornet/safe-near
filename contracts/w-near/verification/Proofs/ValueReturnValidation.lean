import Harness.Main

/-! Reproducible executable validation of deployed f260 before its semantic
contract. This is a test module, not imported by the proof modules.
Run from contracts/w-near/verification:
    lake env lean Proofs/ValueReturnValidation.lean
The independent gas oracle includes the root activation and data-receipt fees.
-/
namespace WNear.Proofs.ValueReturnValidation
open Wasm Wasm.Near WNear.Testing

def check (h : Harness) (label : String) (store : Store NearState) (args : List Value) : IO Unit := do
  let len := u64Arg args 1
  let ptr := u64Arg args 2
  let expected := h.read store ptr len
  let result := h.call store 260 args
  let fees := store.host.fees.newDataReceiptByte
  let dataCost := (store.host.outputDataReceivers.map fun receiver =>
    fees.send (receiver == store.host.context.currentAccountId) * len + fees.execution * len).sum
  let expectedGas := op h 14 + store.host.extCosts.cost "base" +
    store.host.extCosts.cost "read_memory_base" + store.host.extCosts.cost "read_memory_byte" * len + dataCost
  let returned := match result.ending with | .returned [] => true | _ => false
  if !returned || result.after.host.returnData != some expected ||
      result.after.host.returnedPromise.isSome || result.gas != expectedGas then
    throw (IO.userError s!"f260 failure {label}, len={len}, gas={result.gas}, expected={expectedGas}")
  if (changedBytes (h.mem store) (h.mem result.after)).length != 0 then
    throw (IO.userError s!"f260 changed memory: {label}")
  if label == "ft_total_supply" then
    IO.println s!"f260 actual totalSupply capture: len={len}, ptr={ptr}, gas={result.gas}, expected={expectedGas}"

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok m => pure m
    | .error e => throw (IO.userError e.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [260]
  let captures := seen.getD 260 #[]
  if captures.isEmpty then throw (IO.userError "no actual value_return leaf capture")
  let mut checked := 0
  for (method, entry) in captures do
    check h method entry.store entry.args
    checked := checked + 1
  for len in [0, 1, 26, 255, 4096] do
    let bytes := (List.range len).map (fun i => UInt8.ofNat (17 * i + 3))
    let store ← orThrow (h.write h.store 3 bytes)
    let store := { store with host := { store.host with
      outputDataReceivers := [store.host.context.currentAccountId, "other.near".toUTF8.toList],
      returnedPromise := some 0 } }
    check h s!"data-receipt fixture {len}" store [i32 (2 ^ 32 - 1), i64 len, i64 3]
    checked := checked + 1
  IO.println s!"PASS f260 actual host-dispatch: {checked} checks ({captures.size} captures), exact returned bytes and gas"

#eval validate

end WNear.Proofs.ValueReturnValidation
