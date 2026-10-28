import Proofs.StateDecodePrefixLeavesWordResult
import Proofs.StateDecodePrefixLeavesRecordResult
import Proofs.RegisterHostValidation

/-! Independent prefix-leaf replay, including exact boundary and unsigned values. -/
namespace WNear.Proofs.StateDecodePrefixLeavesValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def check (h : Harness) (index : Nat) (entry : Entry) : IO Unit := do
  let memory:=h.mem entry.store
  let ptr:=UInt32.ofNat (u32Arg entry.args 0)
  let len:=UInt32.ofNat (u32Arg entry.args 1)
  let expected:=if index==764 then writeI32 (writeI32 memory ptr.toNat 0) (ptr.toNat+4) len else memory
  let result:=h.call entry.store index entry.args
  let values:=if index==764 then [] else [Value.i64 (UInt64.ofNat ((readI32 memory ptr.toNat).toNat*256))]
  match result.ending with
  | .returned actual=>if actual != values then throw (IO.userError s!"f{index} exact returned packed word mismatch")
  | _=>throw (IO.userError s!"f{index} did not return")
  if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
    throw (IO.userError s!"f{index} whole memory/max mismatch")
  if h.global result.after 0 != h.global entry.store 0 ||result.after.host.context.usedGas != entry.store.host.context.usedGas ||
      result.after.host.gas.promises != entry.store.host.gas.promises ||result.after.host.returnData != entry.store.host.returnData then
    throw (IO.userError s!"f{index} SP/functional host mismatch")
  let units:=if index==764 then 15 else 25
  if result.gas != op h units then throw (IO.userError s!"f{index} exact gas mismatch")
  RegisterHostValidation.fuelBoundary h index (if index==764 then 7 else 20) entry

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [764,765]
  for index in [764,765] do
    let mut captures:=0
    let mut outside:=0
    for (_,entry) in seen.getD index #[] do
      let ptr:=u32Arg entry.args 0
      if (index==765 &&u32Arg entry.args 1 != 4) ||ptr+(if index==764 then 8 else 4)>h.memSize entry.store then
        outside:=outside+1;continue
      check h index entry
      captures:=captures+1
    let mut generated:=0
    for ptr in [0,1,65535,h.memSize h.store-(if index==764 then 8 else 4)] do
      for word in [0,1,2147483648,4294967295] do
        let memory:=if index==765 then writeI32 (h.mem h.store) ptr (UInt32.ofNat word) else h.mem h.store
        let entry:Entry:={store:=h.setMem h.store memory,args:=[.i32 (UInt32.ofNat ptr),.i32 (UInt32.ofNat (if index==764 then word else 4))]}
        check h index entry
        generated:=generated+1
    if captures==0 then throw (IO.userError s!"f{index} lacks captures")
    IO.println s!"PASS prefix f{index}: {captures} accepted captures ({outside} outside),{generated} generated boundaries/unsigned words, whole memory/max/SP/host/exactgas/fuel/one-less"
#eval validate
end WNear.Proofs.StateDecodePrefixLeavesValidation
