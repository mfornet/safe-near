import Proofs.AllocatePositiveValidation
import Proofs.RegisterHostValidation
import Proofs.DeallocateAlignNative

/-! Independent replay of deployed raw-allocation wrappers. The oracle follows
layout, allocator and record writes in instruction order. -/
namespace WNear.Proofs.StateDecodeRawValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def expected (h : Harness) (index : Nat) (entry : Entry) : Option Memory := do
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

private def check (h : Harness) (index units steps : Nat) (entry : Entry) (memory : Memory) : IO Unit := do
  let result:=h.call entry.store index entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError s!"f{index} did not return void")
  if (h.mem result.after).pages != memory.pages || (h.mem result.after).max != memory.max then
    throw (IO.userError s!"f{index} sequential whole-memory mismatch")
  if h.global result.after 0 != h.global entry.store 0 then
    throw (IO.userError s!"f{index} SP mismatch")
  if result.gas != op h units then
    throw (IO.userError s!"f{index} gas got{result.gas/(op h 1)} expected{units}")
  RegisterHostValidation.fuelBoundary h index steps entry

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [767,769,770]
  for (index,units,steps) in [(770,412,329),(769,446,354),(767,584,469)] do
    let mut checked:=0
    let mut getter:=0
    let mut outside:=0
    let mut fixture : Option Entry:=none
    for (method,entry) in seen.getD index #[] do
      let some memory:=expected h index entry | outside:=outside+1;continue
      check h index units steps entry memory
      checked:=checked+1
      if method=="ft_total_supply" then
        getter:=getter+1
        fixture:=some entry
    if checked==0 ||getter==0 then throw (IO.userError s!"f{index} lacks accepted getter capture")
    let mut generated:=0
    if index != 769 then
      let some entry:=fixture | throw (IO.userError "missing raw fixture")
      let sp:=h.stackPointer entry.store
      let head:=(readI32 (h.mem entry.store) 1074896).toNat
      for size in [1,2,3,4,5,16,24,128] do
        for out in [0,sp-64,sp-48,sp-40,sp-16,sp+1,head,65535,h.memSize entry.store-8,u32Arg entry.args 0] do
          let args:=entry.args.set 0 (.i32 (UInt32.ofNat out)) |>.set 1 (.i32 (UInt32.ofNat size))
          let trial:Entry:={entry with args}
          let some memory:=expected h index trial | throw (IO.userError "generated raw case outside direct branch")
          check h index units steps trial memory
          generated:=generated+1
    IO.println s!"PASS raw f{index}: {checked} direct captures ({getter} getter,{outside} outside), {generated} generated output aliases/boundaries, exact whole memory/max/SP,{units}root gas/{steps}steps/one-less"
#eval validate
end WNear.Proofs.StateDecodeRawValidation
