import Proofs.RegisterHostValidation
import Binary.StateDecodeSlices
import NearVM.MeteredI32MemoryRules

/-! Independent replay of actual361/362 accepted slice splits, including empty
and full splits and wrapping source-pointer arithmetic. This executable evidence
is separate from the kernel WP; no source-pointer span is required by these helpers. -/
namespace WNear.Proofs.StateDecodeSlicesValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def check (h : Harness) (drop : Bool) (entry : Entry) (label : String) : IO Unit := do
  let index := if drop then 361 else 362
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let pointer := UInt32.ofNat (u32Arg entry.args 1)
  let len := UInt32.ofNat (u32Arg entry.args 2)
  let split := UInt32.ofNat (u32Arg entry.args 3)
  let before := h.mem entry.store
  if split.toNat>len.toNat ||out.toNat+8>before.byteSize then
    throw (IO.userError s!"invalid accepted fixture {label}")
  -- Independent high-first, low-second replay of the actual instructions.
  let high := if drop then len-split else split
  let low := if drop then pointer+split else pointer
  let expected := writeI32 (writeI32 before (out.toNat+4) high) out.toNat low
  let result := h.call entry.store index entry.args
  match result.ending with
  | .returned [] => pure ()
  | _ => throw (IO.userError s!"f{index}/{label} expected void return: {result.ending.describe}")
  if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
    throw (IO.userError s!"f{index}/{label} whole-memory/max mismatch")
  if readI32 (h.mem result.after) out.toNat != low ||readI32 (h.mem result.after) (out.toNat+4) != high then
    throw (IO.userError s!"f{index}/{label} output-word mismatch")
  if h.stackPointer result.after != h.stackPointer entry.store ||
      result.after.host.gas.promises != entry.store.host.gas.promises ||
      result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
      result.after.host.context.usedGas != entry.store.host.context.usedGas ||
      result.after.host.returnData != entry.store.host.returnData ||
      result.after.host.returnedPromise != entry.store.host.returnedPromise ||
      result.after.host.logs != entry.store.host.logs then
    throw (IO.userError s!"f{index}/{label} SP/observer frame mismatch")
  let units := if drop then 25 else 21
  if result.gas != op h units then throw (IO.userError s!"f{index}/{label} exactgas got{result.gas},expected{op h units}")
  RegisterHostValidation.fuelBoundary h index (if drop then 16 else 12) entry

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [361,362]
  for drop in [true,false] do
    let index := if drop then 361 else 362
    let mut captures := 0
    let mut getter := 0
    let mut outside := 0
    for (method,entry) in seen.getD index #[] do
      if u32Arg entry.args 3>u32Arg entry.args 2 then
        outside:=outside+1
        continue
      check h drop entry s!"capture {method}"
      captures:=captures+1
      if method=="ft_total_supply" then getter:=getter+1
    -- Full-range lengths, arbitrary non-dereferenced pointers, unaligned outputs,
    -- a cross-page output and the exact final eight writable bytes.
    let memory := h.mem h.store
    let outputs := [0,1,65532,memory.byteSize-8,h.stackPointer h.store-32]
    let pointers : List UInt32 := [0,1,65535,67108864,4294967292,4294967295]
    let lengths : List UInt32 := [0,1,4,29,4294967295]
    let mut generated := 0
    let mut zeroSplit := 0
    let mut fullSplit := 0
    let mut wrapping := 0
    for out in outputs do
      for pointer in pointers do
        for len in lengths do
          for split in [0,len,UInt32.ofNat (len.toNat/2)] do
            let entry : Entry := {store:=h.store,args:=[.i32 (UInt32.ofNat out),.i32 pointer,.i32 len,.i32 split,.i32 1056580]}
            check h drop entry s!"synthetic {generated}"
            generated:=generated+1
            if split==0 then zeroSplit:=zeroSplit+1
            if split==len then fullSplit:=fullSplit+1
            if drop &&pointer.toNat+split.toNat≥2^32 then wrapping:=wrapping+1
    if generated != 450 ||zeroSplit==0 ||fullSplit==0 ||(drop &&wrapping==0) then
      throw (IO.userError s!"f{index} boundary fixture coverage failed")
    if getter==0 then throw (IO.userError s!"missing actual getter f{index} capture")
    IO.println s!"PASS actual f{index}: {captures} accepted captures ({getter} getter,{outside} outside),{generated} generated incl split0={zeroSplit}/splitlen={fullSplit}/wrappedptr={wrapping}; wholememory/max/SP/observer/exactgas/fuel/one-less"
#eval validate
end WNear.Proofs.StateDecodeSlicesValidation
