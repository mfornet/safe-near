import Proofs.StateDecodeVectorMemory
import Proofs.AllocatePositiveValidation
import Proofs.RegisterHostValidation

/-! Independent accepted316/315 replay from original bytes and raw heap writes. -/
namespace WNear.Proofs.StateDecodePrefixValidation
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

private def check (h : Harness) (index : Nat) (entry : Entry) : IO Bool := do
  let some memory:=expected h index entry | return false
  let slice:=u32Arg entry.args 1
  let ptr:=(readI32 (h.mem entry.store) slice).toNat
  let n:=(readI32 (h.mem entry.store) ptr).toNat
  let result:=h.call entry.store index entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError s!"f{index} did not return void")
  if (h.mem result.after).pages != memory.pages ||(h.mem result.after).max != memory.max then
    throw (IO.userError s!"f{index} whole sequential memory/max mismatch")
  if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError s!"f{index} SP mismatch")
  let units:=18*n+(if index==316 then 919 else 971)
  let steps:=17*n+(if index==316 then 726 else 770)
  if result.gas != op h units then throw (IO.userError s!"f{index} gas got{result.gas/(op h 1)},expected{units}")
  RegisterHostValidation.fuelBoundary h index steps entry
  return true

def validate : IO Unit := do
  let protocol←RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes←IO.FS.readBinFile "../contract.wasm"
  let module←orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h←orThrow (Harness.load protocol module internalContext [])
  let seen←captureAll protocol module bytes.size [315,316]
  for index in [315,316] do
    let mut captures:=0
    let mut getter:=0
    let mut outside:=0
    let mut fixture:Option Entry:=none
    for (method,entry) in seen.getD index #[] do
      if ←check h index entry then
        captures:=captures+1
        if method=="ft_total_supply" then getter:=getter+1;fixture:=some entry
      else outside:=outside+1
    let some entry:=fixture | throw (IO.userError s!"f{index} lacks accepted getter capture")
    let sp:=h.stackPointer entry.store
    let slice:=u32Arg entry.args 1
    let ptr:=(readI32 (h.mem entry.store) slice).toNat
    let mut generated:=0
    for size in [1,2,3,4,5,16,24,128] do
      for extra in [0,1,17] do
        let source:=if ptr+4+size+extra≤h.memSize entry.store then ptr else ptr-512
        let base:=(h.mem entry.store).writeList (source+4) ((List.range (size+extra)).map (fun i=>UInt8.ofNat (17*i+1)))
        let initial:=writeI32 (writeI32 (writeI32 base source (UInt32.ofNat size)) slice (UInt32.ofNat source)) (slice+4) (UInt32.ofNat (size+extra+4))
        for out in [u32Arg entry.args 0,sp+1,slice-4,slice,slice+1,ptr,ptr+1,h.memSize entry.store-16] do
          let sample:Entry:={entry with store:=h.setMem entry.store initial,args:=[.i32 (UInt32.ofNat out),.i32 (UInt32.ofNat slice)]}
          if !(←check h index sample) then throw (IO.userError s!"generated f{index} outside accepted direct geometry size{size}/extra{extra}/out{out}")
          generated:=generated+1
    IO.println s!"PASS f{index}: {captures} accepted captures ({getter} getter,{outside} outside),{generated} generated aliases/boundaries; whole memory/max/SP/exactgas/fuel/one-less"
#eval validate
end WNear.Proofs.StateDecodePrefixValidation
