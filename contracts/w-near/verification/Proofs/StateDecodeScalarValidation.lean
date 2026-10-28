import NearVM.MeteredI32MemoryRules
import NearVM.MeteredScalarRules
import Proofs.RegisterHostValidation
import Binary.StateDecodeScalar
import NearVM.MeteredByteMemoryRules

/-! Independent complete replay of accepted deployed372/371 scalar decoders.
The oracle follows every intermediate memory, cache, descriptor and tag write;
source, descriptor and output may overlap under the original native geometry. -/
namespace WNear.Proofs.StateDecodeScalarValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def accepted (h : Harness) (wide : Bool) (entry : Entry) : Bool := Id.run do
  let memory := h.mem entry.store
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let slice := UInt32.ofNat (u32Arg entry.args 1)
  let sp := h.stackPointer entry.store
  let pointer := readI32 memory slice.toNat
  let len := readI32 memory (slice.toNat+4)
  let width := if wide then 16 else 8
  return decide memory.wf &&decide (memory.byteSize≤2^32) &&decide (48≤sp) &&decide (sp≤memory.byteSize) &&
    decide (sp≤out.toNat) &&decide (out.toNat+(if wide then 24 else 16)≤memory.byteSize) &&
    decide (sp≤slice.toNat) &&decide (slice.toNat+8≤memory.byteSize) &&decide (width≤len.toNat) &&
    decide (sp≤pointer.toNat) &&decide (pointer.toNat+width≤memory.byteSize)

private def expected (h : Harness) (wide : Bool) (entry : Entry) : Memory := Id.run do
  let original := h.mem entry.store
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let slice := UInt32.ofNat (u32Arg entry.args 1)
  let scratch := UInt32.ofNat (h.stackPointer entry.store)-48
  let width : UInt32 := if wide then 16 else 8
  let takeOut := scratch+(if wide then 8 else 16)
  let wordOut := scratch+(if wide then 16 else 24)
  let dropOut := scratch+(if wide then 0 else 8)
  let len := readI32 original (slice.toNat+4)
  let pointer := readI32 original slice.toNat
  -- Actual362 takes a slice: high length then low pointer.
  let mut memory := writeI32 (writeI32 original (takeOut.toNat+4) width) takeOut.toNat pointer
  let source := readI32 memory takeOut.toNat
  -- Actual694/710 writes the low word first, then reads/writes the high word.
  memory:=writeI64 memory (wordOut.toNat+1) (readI64 memory source.toNat)
  if wide then memory:=writeI64 memory (wordOut+9).toNat (readI64 memory (source+8).toNat)
  memory:=writeByte memory wordOut.toNat 0
  let high := if wide then readI64 memory (scratch+25).toNat else 0
  let low := readI64 memory (scratch.toNat+(if wide then 17 else 25))
  -- Actual361 re-reads the original descriptor on this current memory.
  let remainingPointer := readI32 memory slice.toNat
  let remainingLength := readI32 memory (slice.toNat+4)
  memory:=writeI32 (writeI32 memory (dropOut.toNat+4) (remainingLength-width)) dropOut.toNat (remainingPointer+width)
  let remainder := readI64 memory (scratch.toNat+(if wide then 0 else 8))
  if wide then memory:=writeI64 memory (out+16).toNat high
  memory:=writeI64 memory (out+8).toNat low
  memory:=writeI64 memory slice.toNat remainder
  memory:=writeI32 memory out.toNat 0
  -- len participates in the original guard even if later aliases overwrite it.
  let _ := len
  return memory

private def check (h : Harness) (wide : Bool) (entry : Entry) (label : String) : IO Unit := do
  let index := if wide then 372 else 371
  if !accepted h wide entry then throw (IO.userError s!"f{index}/{label} fixture outside original Native")
  let memory := expected h wide entry
  let result := h.call entry.store index entry.args
  match result.ending with
  | .returned [] => pure ()
  | _ => throw (IO.userError s!"f{index}/{label} did not return void: {result.ending.describe}")
  if (h.mem result.after).pages != memory.pages ||(h.mem result.after).max != memory.max then
    throw (IO.userError s!"f{index}/{label} whole sequential memory/max mismatch")
  if h.stackPointer result.after != h.stackPointer entry.store ||
      result.after.host.gas.promises != entry.store.host.gas.promises ||
      result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
      result.after.host.context.usedGas != entry.store.host.context.usedGas ||
      result.after.host.returnData != entry.store.host.returnData ||
      result.after.host.returnedPromise != entry.store.host.returnedPromise ||
      result.after.host.logs != entry.store.host.logs then
    throw (IO.userError s!"f{index}/{label} SP/observer frame mismatch")
  let units := if wide then 167 else 150
  if result.gas != op h units then throw (IO.userError s!"f{index}/{label} gas got{result.gas},expected{op h units} ({units}op)")
  RegisterHostValidation.fuelBoundary h index (if wide then 133 else 117) entry

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [371,372]
  for wide in [true,false] do
    let index := if wide then 372 else 371
    let mut captures := 0
    let mut getter := 0
    let mut outside := 0
    for (method,entry) in seen.getD index #[] do
      if !accepted h wide entry then
        outside:=outside+1
        continue
      check h wide entry s!"capture {method}"
      captures:=captures+1
      if method=="ft_total_supply" then getter:=getter+1
    let top := h.memSize h.store
    let width := if wide then 16 else 8
    let outWidth := if wide then 24 else 16
    let placements := [(48,48,48,48),(1024,1088,1152,1216),(1024,1088,1152,1152),
      (1024,1088,1152,1088),(1024,1088,1152,1155),(1024,1088,1152,1091),
      (1024,1156,1152,1216),(1024,1148,1152,1216),(1024,1024,1025,1024),
      (65520,65535,65540,65530),(1024,top-8,top-width,top-outWidth),
      (top-128,top-112,top-64,top-outWidth)]
    let mut generated := 0
    for (sp,slice,pointer,out) in placements do
      for len in [width,width+1,29,4294967295] do
        for seed in [0,1,255] do
          let initial := h.setGlobal h.store 0 (.i32 (UInt32.ofNat sp))
          let pattern := (List.range width).map (fun i=>UInt8.ofNat (seed+17*i))
          let payload := (h.mem initial).writeList pointer pattern
          let descriptor := writeI32 (writeI32 payload (slice+4) (UInt32.ofNat len)) slice (UInt32.ofNat pointer)
          let entry : Entry := {store:=h.setMem initial descriptor,args:=[.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat slice)]}
          check h wide entry s!"generated {generated}"
          generated:=generated+1
    if captures==0 ||getter==0 ||generated != 144 then throw (IO.userError s!"f{index} scalar validation coverage failed")
    IO.println s!"PASS actual scalar f{index}: {captures} accepted captures ({getter} getter,{outside} outside),{generated} generated alias/boundary cases; whole sequential memory/max/SP/observer/exactgas/fuel/one-less"
#eval validate
end WNear.Proofs.StateDecodeScalarValidation
