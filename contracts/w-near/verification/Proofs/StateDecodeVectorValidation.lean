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

private def expectedVector (h : Harness) (entry : Entry) : Option Memory := do
  let sp:=h.stackPointer entry.store
  let out:=UInt32.ofNat (u32Arg entry.args 0)
  let size:=UInt32.ofNat (u32Arg entry.args 1)
  if sp<80 ||out.toNat+12>h.memSize entry.store then none else do
    let child:Entry:={
      store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat (sp-16))),
      args:=[.i32 (UInt32.ofNat (sp-8)),.i32 size,.i32 0]}
    let memory ←expectedRaw h 767 child
    let packed:=readI64 memory (sp-8)
    return writeI64 (writeI32 memory (out.toNat+8) 0) out.toNat packed

private def check (h : Harness) (index : Nat) (entry : Entry) : IO Bool := do
  let out:=u32Arg entry.args 0
  let size:=u32Arg entry.args (if index==373 then 1 else 2)
  let vector:Entry:={entry with args:=[.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat size)]}
  let some initial:=expectedVector h vector | return false
  let mut expected:=initial
  if index==374 then
    let source:=u32Arg entry.args 1
    let dest:=(readI32 initial out).toNat
    if source+size>initial.byteSize ||dest+size>initial.byteSize then return false
    -- The actual951 loop reads each byte from the current memory.
    for i in [0:size] do expected:=writeByte expected (dest+i) (UInt32.ofNat (expected.read8 (source+i)).toNat)
    expected:=writeI32 expected (out+8) (UInt32.ofNat size)
  let result:=h.call entry.store index entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError s!"f{index} did not return void")
  if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
    throw (IO.userError s!"f{index} whole sequential memory/max mismatch")
  if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError s!"f{index} SP mismatch")
  let units:=if index==373 then 619 else 18*size+657
  let steps:=if index==373 then 494 else 17*size+518
  if result.gas != op h units then throw (IO.userError s!"f{index} gas got{result.gas/(op h 1)},expected{units}")
  RegisterHostValidation.fuelBoundary h index steps entry
  return true

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [373,374]
  for index in [373,374] do
    let mut captures:=0
    let mut getter:=0
    let mut outside:=0
    let mut fixture:Option Entry:=none
    for (method,entry) in seen.getD index #[] do
      if ←check h index entry then
        captures:=captures+1
        if method=="ft_total_supply" then getter:=getter+1;fixture:=some entry
      else outside:=outside+1
    let some entry:=fixture | throw (IO.userError s!"f{index} lacks direct getter capture")
    let sp:=h.stackPointer entry.store
    let head:=(readI32 (h.mem entry.store) 1074896).toNat
    let mut generated:=0
    for size in [1,2,3,4,5,16,24,128] do
      for out in [0,sp-80,sp-64,sp-48,sp-8,sp+1,head,65535,h.memSize entry.store-12,u32Arg entry.args 0] do
        let sources:=if index==373 then [0] else [u32Arg entry.args 1,sp-64,head,h.memSize entry.store-size]
        for source in sources do
          if index==374 &&source+size>h.memSize entry.store then continue
          let args:=if index==373 then [.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat size)]
            else [.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat source),.i32 (UInt32.ofNat size)]
          if !(←check h index {entry with args}) then throw (IO.userError s!"generated f{index} outside direct geometry")
          generated:=generated+1
    if index==374 then
      for size in [1,2,3,4,5,16,24,128] do
        let normal:Entry:={entry with args:=[.i32 (UInt32.ofNat (u32Arg entry.args 0)),.i32 (UInt32.ofNat size)]}
        let some memory:=expectedVector h normal | throw (IO.userError "cannot derive generated allocation destination")
        let dest:=(readI32 memory (u32Arg entry.args 0)).toNat
        let seeded:Entry:={entry with store:=h.setMem entry.store ((h.mem entry.store).writeList dest ((List.range size).map (fun i=>UInt8.ofNat (17*i+1))))}
        for out in [dest-8,dest,dest+1] do
          for source in [dest-1,dest,dest+1] do
            let args:=[Value.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat source),.i32 (UInt32.ofNat size)]
            if !(←check h index {seeded with args}) then throw (IO.userError "generated overlapping copy outside original bounds")
            generated:=generated+1
    IO.println s!"PASS f{index}: {captures} direct captures ({getter} getter,{outside} outside),{generated} generated aliases/boundaries; whole memory/max/SP/exactgas/fuel/one-less"
#eval validate
end WNear.Proofs.StateDecodeVectorValidation
