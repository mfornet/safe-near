import Proofs.StateDecodeVectorMemory
import Proofs.AllocatePositiveValidation
import Proofs.RegisterHostValidation

/-! Independent accepted316/315 replay from original bytes and raw heap writes. -/
namespace WNear.Proofs.StateDecodeBorshValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def expectedRaw (h : Harness) (index : Nat) (entry : Entry) : Option Memory := do
  let mut memory := h.mem entry.store
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let size := UInt32.ofNat (u32Arg entry.args 1)
  let sp := UInt32.ofNat (h.stackPointer entry.store)
  if size==0 || size.toNat≥2^31 then none else do
    if index==767 then
      if u32Arg entry.args 2  !=  0 then none else pure ()
    else
      if u32Arg entry.args 2  !=  1 then none else pure ()
      if index==770 &&u32Arg entry.args 3  !=  0 then none else pure ()
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
      if index  !=  770 then
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

private def expectedPrefix (h : Harness) (entry : Entry) : Option Memory := do
  let mut m := h.mem entry.store
  let sp := h.stackPointer entry.store
  let r := sp-64
  let out := u32Arg entry.args 0
  let slice := u32Arg entry.args 1
  let ptr := readI32 m slice
  let len := readI32 m (slice+4)
  let n := (readI32 m ptr.toNat).toNat
  if sp<144 ||out<sp ||slice<sp ||out+16>m.byteSize ||slice+8>m.byteSize ||ptr.toNat<sp ||n==0 ||n≥2^31 ||len.toNat<4+n ||ptr.toNat+4+n>m.byteSize then none else do
    m:=writeI32 (writeI32 m (r+44) 4) (r+40) ptr
    m:=writeI32 (writeI32 m (r+36) (len-4)) (r+32) (ptr+4)
    m:=writeI64 m slice (readI64 m (r+32))
    m:=writeI32 (writeI32 m (r+24) 0) (r+28) (UInt32.ofNat n)
    m:=writeI32 (writeI32 m (r+20) (UInt32.ofNat n)) (r+16) (ptr+4)
    let child:Entry:={
      store:=h.setMem (h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))) m
      args:=[.i32 (UInt32.ofNat (r+48)),.i32 (UInt32.ofNat n)]}
    m←expectedVector h child
    let dest:=(readI32 m (r+48)).toNat
    if dest+n>m.byteSize then none else do
      for i in [0:n] do m:=writeByte m (dest+i) (UInt32.ofNat (m.read8 (ptr.toNat+4+i)).toNat)
      m:=writeI32 m (r+56) (UInt32.ofNat n)
      let currentPtr:=readI32 m slice
      let currentLen:=readI32 m (slice+4)
      if currentLen.toNat<n then none else do
        m:=writeI32 (writeI32 m (r+12) (currentLen-UInt32.ofNat n)) (r+8) (currentPtr+UInt32.ofNat n)
        let remainder:=readI64 m (r+8)
        m:=writeI32 m (out+12) (readI32 m (r+56))
        m:=writeI64 m (out+4) (readI64 m (r+48))
        m:=writeI32 m out 0
        return writeI64 m slice remainder

private def expected (h : Harness) (index : Nat) (entry : Entry) : Option Memory := do
  if index==316 then expectedPrefix h entry else do
    let sp:=h.stackPointer entry.store
    let r:=sp-16
    let child:Entry:={
      store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))
      args:=[.i32 (UInt32.ofNat r),.i32 (UInt32.ofNat (u32Arg entry.args 1))]}
    -- The316 caller output is its parent's scratch, above its own entry SP.
    let m←expectedPrefix h child
    let packed:=readI64 m (r+4)
    let high:=readI32 m (r+12)
    let out:=u32Arg entry.args 0
    return writeI32 (writeI32 (writeI64 m (out+4) packed) (out+12) high) out 0


private def expectedScalar (h : Harness) (wide : Bool) (entry : Entry) : Memory := Id.run do
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

private def expectedBorsh (h:Harness) (entry:Entry):Option Memory:=do
  let sp:=h.stackPointer entry.store
  let r:=sp-96
  let out:=u32Arg entry.args 0
  let slice:=u32Arg entry.args 1
  let original:=h.mem entry.store
  let ptr:=(readI32 original slice).toNat
  let len:=(readI32 original (slice+4)).toNat
  let n:=(readI32 original ptr).toNat
  if sp<256 ||out<sp ||out+44>original.byteSize ||slice<sp ||ptr<sp ||len<4+n+24 ||ptr+4+n+24>original.byteSize then none else do
    let child:Entry:={
      store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))
      args:=[.i32 (UInt32.ofNat (r+56)),.i32 (UInt32.ofNat slice)]}
    let mut m←expected h 315 child
    let prefixWord:=readI64 m (r+60)
    m:=writeI32 m (r+24) (readI32 m (r+68))
    m:=writeI64 m (r+16) prefixWord
    let wide:Entry:={child with store:=h.setMem child.store m}
    m:=expectedScalar h true wide
    m:=writeI64 m (r+40) (readI64 m (r+68))
    m:=writeI32 m (r+48) (readI32 m (r+76))
    m:=writeI64 m (r+32) (readI64 m (r+60))
    let high:=readI64 m (r+44)
    let low:=readI64 m (r+36)
    let narrow:Entry:={child with store:=h.setMem child.store m}
    m:=expectedScalar h false narrow
    m:=writeI32 m (r+88) (readI32 m (r+68))
    m:=writeI64 m (r+80) (readI64 m (r+60))
    let length:=readI32 m (r+24)
    m:=writeI32 m (r+8) length
    let packed:=readI64 m (r+16)
    m:=writeI64 m r packed
    let usage:=readI64 m (r+84)
    m:=writeI64 m (out+16) high
    m:=writeI64 m (out+8) low
    m:=writeI64 m (out+24) usage
    m:=writeI64 m (out+32) packed
    m:=writeI32 m (out+40) length
    return writeI32 m out 0

private def check (h:Harness) (entry:Entry):IO Bool:=do
  let some memory:=expectedBorsh h entry | return false
  let slice:=u32Arg entry.args 1
  let ptr:=(readI32 (h.mem entry.store) slice).toNat
  let n:=(readI32 (h.mem entry.store) ptr).toNat
  let result:=h.call entry.store 425 entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError "f425 did not return void")
  if (h.mem result.after).pages != memory.pages ||(h.mem result.after).max != memory.max then
    throw (IO.userError "f425 whole sequential memory/max mismatch")
  if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError "f425 SP mismatch")
  let units:=18*n+1448
  if result.gas != op h units then throw (IO.userError s!"f425 gas got{result.gas/(op h 1)},expected{units}")
  RegisterHostValidation.fuelBoundary h 425 (17*n+1171) entry
  return true

def validate:IO Unit:=do
  let protocol←RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes←IO.FS.readBinFile "../contract.wasm"
  let module←orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h←orThrow (Harness.load protocol module internalContext [])
  let seen←captureAll protocol module bytes.size [425]
  let mut captures:=0
  let mut getter:=0
  let mut outside:=0
  let mut fixture:Option Entry:=none
  for (method,entry) in seen.getD 425 #[] do
    if ←check h entry then
      captures:=captures+1
      if method=="ft_total_supply" then getter:=getter+1;fixture:=some entry
    else outside:=outside+1
  let some entry:=fixture | throw (IO.userError "f425 lacks accepted getter capture")
  let sp:=h.stackPointer entry.store
  let slice:=u32Arg entry.args 1
  let ptr:=(readI32 (h.mem entry.store) slice).toNat
  let mut generated:=0
  for size in [1,2,3,4,5,16,24,128] do
    for extra in [0,1,17] do
      let source:=if ptr+4+size+24+extra≤h.memSize entry.store then ptr else ptr-1024
      let base:=(h.mem entry.store).writeList (source+4) ((List.range (size+24+extra)).map (fun i=>UInt8.ofNat (17*i+1)))
      let initial:=writeI32 (writeI32 (writeI32 base source (UInt32.ofNat size)) slice (UInt32.ofNat source)) (slice+4) (UInt32.ofNat (size+24+extra+4))
      for out in [u32Arg entry.args 0,sp+1,slice-8,slice,slice+1,source-16,source-15,h.memSize entry.store-44] do
        let sample:Entry:={entry with store:=h.setMem entry.store initial,args:=[.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat slice)]}
        if !(←check h sample) then throw (IO.userError s!"generated f425 outside accepted direct geometry size{size}/extra{extra}/out{out}")
        generated:=generated+1
  IO.println s!"PASS f425: {captures} accepted captures ({getter} getter,{outside} outside),{generated} generated aliases/boundaries; whole memory/max/SP/exactgas/fuel/one-less"
#eval validate
end WNear.Proofs.StateDecodeBorshValidation
