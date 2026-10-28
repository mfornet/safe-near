import Proofs.StateDecodeVectorMemory
import Proofs.AllocatePositiveValidation
import Proofs.RegisterHostValidation

/-! Independent f373 replay through original-memory raw allocator writes. -/
namespace WNear.Proofs.StateDecodeVectorValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def expectedRaw (h : Harness) (index : Nat) (entry : Entry) : Option Memory := do
  let mut memory := h.mem entry.store
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let size := UInt32.ofNat (u32Arg entry.args 1)
  let sp := UInt32.ofNat (h.stackPointer entry.store)
  if size==0 || size.toNat≥2^31 then none else do
    if index==767 then
      if u32Arg entry.args 2 != 0 then none else pure ()
    else
      if u32Arg entry.args 2 != 1 then none else pure ()
      if index==770 &&u32Arg entry.args 3 != 0 then none else pure ()
    if index==767 then
      let wrapperScratch := sp-48
      memory:=writeI32 memory (wrapperScratch.toNat+12) 1
      memory:=writeI32 memory (wrapperScratch.toNat+8) size
      memory:=writeI32 memory (wrapperScratch.toNat+4) 1
      memory:=writeI32 memory wrapperScratch.toNat size
      memory:=writeI64 memory ((sp-32).toNat+24) (readI64 memory wrapperScratch.toNat)
    let allocSP := if index==767 then sp-48 else if index==769 then sp-16 else sp
    let saved := writeI32 memory ((allocSP-16).toNat+12) (readI32 memory 1074896)
    let head := readI32 saved ((allocSP-16).toNat+12)
    let words := DeallocateAlign.quotient size 4
    if head==0 || !AllocateValidation.native saved head words then none else do
      let ptr := Allocate.splitPointer saved head words
      let split := AllocateValidation.splitMemory saved head words
      memory:=writeI32 split 1074896 (readI32 split ((allocSP-16).toNat+12))
      let recordOut := if index==767 then sp-40 else if index==769 then sp-8 else out
      memory:=writeI32 memory (recordOut.toNat+4) size
      memory:=writeI32 memory recordOut.toNat ptr
      if index != 770 then
        let copyOut := if index==767 then sp-16 else out
        memory:=writeI32 memory copyOut.toNat (readI32 memory recordOut.toNat)
        memory:=writeI32 memory (copyOut.toNat+4) (readI32 memory (recordOut.toNat+4))
        if index==767 then
          let len := readI32 memory ((sp-32).toNat+20)
          let pointer := readI32 memory ((sp-32).toNat+16)
          memory:=writeI32 memory out.toNat pointer
          memory:=writeI32 memory (out.toNat+4) len
      return memory

private def check (h : Harness) (entry : Entry) : IO Bool := do
  let sp:=h.stackPointer entry.store
  let out:=UInt32.ofNat (u32Arg entry.args 0)
  let size:=UInt32.ofNat (u32Arg entry.args 1)
  if sp<80 ||out.toNat+12>h.memSize entry.store then return false
  let child:Entry:={
    store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat (sp-16))),
    args:=[.i32 (UInt32.ofNat (sp-8)),.i32 size,.i32 0]}
  let some memory:=expectedRaw h 767 child | return false
  let packed:=readI64 memory (sp-8)
  let expected:=writeI64 (writeI32 memory (out.toNat+8) 0) out.toNat packed
  let result:=h.call entry.store 373 entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError "f373 did not return void")
  if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
    throw (IO.userError "f373 whole sequential memory/max mismatch")
  if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError "f373 SP mismatch")
  if result.gas != op h 619 then throw (IO.userError s!"f373 gas got{result.gas/(op h 1)},expected619")
  RegisterHostValidation.fuelBoundary h 373 494 entry
  return true

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [373]
  let mut captures:=0
  let mut getter:=0
  let mut outside:=0
  let mut fixture:Option Entry:=none
  for (method,entry) in seen.getD 373 #[] do
    if ←check h entry then
      captures:=captures+1
      if method=="ft_total_supply" then getter:=getter+1;fixture:=some entry
    else outside:=outside+1
  let some entry:=fixture | throw (IO.userError "f373 lacks direct getter capture")
  let sp:=h.stackPointer entry.store
  let head:=(readI32 (h.mem entry.store) 1074896).toNat
  let mut generated:=0
  for size in [1,2,3,4,5,16,24,128] do
    for out in [0,sp-80,sp-64,sp-48,sp-8,sp+1,head,65535,h.memSize entry.store-12,u32Arg entry.args 0] do
      let args:=entry.args.set 0 (.i32 (UInt32.ofNat out)) |>.set 1 (.i32 (UInt32.ofNat size))
      if !(←check h {entry with args}) then throw (IO.userError "generated f373 outside direct geometry")
      generated:=generated+1
  IO.println s!"PASS f373: {captures} direct captures ({getter} getter,{outside} outside),{generated} generated aliases/boundaries; whole memory/max/SP,619root gas/494steps/one-less"
#eval validate
end WNear.Proofs.StateDecodeVectorValidation
