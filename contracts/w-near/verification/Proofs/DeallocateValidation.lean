import Harness.Main
import Proofs.DeallocateCoreState
import Proofs.DeallocateListClear

/-! Exact captured checks for accepted deallocation paths. This executable
suite is separate from the integrated harness and the kernel proofs. -/
namespace WNear.Proofs.DeallocateValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing
open DeallocateCore

def coreNative (p : Layout) : Bool :=
  decide (p.memory.wf) &&
  decide (p.pointer ≠ 0) &&
  decide (p.length ≠ 0) &&
  decide (p.length.toNat + 4 < 2 ^ 32) &&
  decide (p.pointer + 4294967288 = p.header) &&
  decide (p.pointer + 4294967292 = p.previousAddress) &&
  decide (p.allocator.toNat + 4 ≤ p.memory.byteSize) &&
  decide (p.header.toNat + 4 ≤ p.memory.byteSize) &&
  decide (p.pointer.toNat + 4 ≤ p.memory.byteSize) &&
  decide (p.header.toNat + 8 ≤ (DeallocateListSize.endWord (markedMemory p) p.header).toNat) &&
  decide (p.previousAddress.toNat + 4 ≤ (zeroMemory p).byteSize) &&
  decide (Deallocate.previous (zeroMemory p) p.previousAddress = p.previous) &&
  decide (p.previous ≠ 0) &&
  decide (p.previous.toNat + 1 ≤ (zeroMemory p).byteSize) &&
  decide (readByteWord (zeroMemory p) p.previous.toNat &&& 1 = 0) &&
  decide (DeallocateListState.firstLink (unlinkLayout p) ≠ 0) &&
  decide (DeallocateListState.firstRaw (unlinkLayout p) &&& 2 = 0) &&
  decide ((DeallocateListState.firstLink (unlinkLayout p)).toNat + 8 ≤ (zeroMemory p).byteSize) &&
  decide (p.header.toNat + 8 ≤ (zeroMemory p).byteSize) &&
  decide (DeallocateListState.secondLink (unlinkLayout p) ≠ 0) &&
  decide ((DeallocateListState.secondLink (unlinkLayout p)).toNat + 4 ≤ (DeallocateListState.firstMemory (unlinkLayout p)).byteSize) &&
  decide (p.header.toNat + 1 ≤ (unlinkedMemory p).byteSize) &&
  decide (readByteWord (unlinkedMemory p) p.header.toNat &&& 2 = 0) &&
  decide (p.previous.toNat + 4 ≤ (unlinkedMemory p).byteSize) &&
  decide (p.previous.toNat + 8 ≤ (DeallocateListSize.endWord (unlinkedMemory p) p.previous).toNat) &&
  decide (p.allocator.toNat + 4 ≤ (unlinkedMemory p).byteSize)

def listNative (p : DeallocateListState.Layout) : Bool :=
  decide p.memory.wf && decide (p.pointer.toNat + 8 ≤ p.memory.byteSize) &&
  decide (DeallocateListState.firstLink p ≠ 0) && decide (DeallocateListState.firstRaw p &&& 2 = 0) &&
  decide ((DeallocateListState.firstLink p).toNat + 8 ≤ p.memory.byteSize) &&
  decide (DeallocateListState.secondLink p ≠ 0) &&
  decide ((DeallocateListState.secondLink p).toNat + 4 ≤ (DeallocateListState.firstMemory p).byteSize)

def coreLayout (h : Harness) (memory : Memory) (allocator pointer length alignment : UInt32) : Layout :=
  {mi := h.inst, memoryIndex := h.memAddr, allocator, pointer, length, alignment,
   header := pointer + 4294967288, previousAddress := pointer + 4294967292,
   previous := Deallocate.previous memory (pointer + 4294967292), memory,
   address568 := h.inst.funcAddrs[568]!, address570 := h.inst.funcAddrs[570]!,
   address575 := h.inst.funcAddrs[575]!, address576 := h.inst.funcAddrs[576]!}

def checkFuel (h : Harness) (index fuel : Nat) (entry : Entry) : IO Unit := do
  let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[index]! entry.args
    | throw (IO.userError s!"cannot start f{index}")
  match (runInitialized h.cfg.wasm fuel (.next initial)).1 with
  | .done _ _ => pure ()
  | _ => throw (IO.userError s!"f{index} exact fuel mismatch")
  match (runInitialized h.cfg.wasm (fuel - 1) (.next initial)).2 with
  | some (.executionIssue .fuelExhausted) => pure ()
  | _ => throw (IO.userError s!"f{index} one-less-fuel mismatch")

def checkMemory (h : Harness) (index : Nat) (actual : Store NearState) (expected : Memory) : IO Unit := do
  if (h.mem actual).pages != expected.pages || (h.mem actual).max != expected.max then
    throw (IO.userError s!"f{index} exact sequential memory mismatch")

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [68,582,575,576,570,568]
  let mut getterDrops := 0
  for (index, units, fuel) in [(68,318,229),(582,230,189),(575,71,66),(576,24,16),(570,40,24),(568,28,20)] do
    let mut checked := 0
    let mut outside := 0
    for (method, entry) in seen.getD index #[] do
      let memory := h.mem entry.store
      let a := UInt32.ofNat (u32Arg entry.args 0)
      let b := UInt32.ofNat (u32Arg entry.args 1)
      let c := UInt32.ofNat (u32Arg entry.args 2)
      let d := UInt32.ofNat (u32Arg entry.args 3)
      let q : DeallocateListState.Layout := {mi := h.inst, memoryIndex := h.memAddr, pointer := a, memory}
      let core := if index == 68 then coreLayout h memory 1074896
        (readI32 memory a.toNat) (readI32 memory (a.toNat+4)) 1 else coreLayout h memory a b c d
      let accepted := if index == 68 || index == 582 then coreNative core else
        if index == 575 then listNative q else
        if index == 576 then decide (a.toNat + 4 ≤ memory.byteSize) && decide (a.toNat + 8 ≤ (DeallocateListSize.endWord memory a).toNat) else
        if index == 570 then decide (a.toNat + 4 < 2^32) else decide (0 < b.toNat) && decide (a.toNat+b.toNat < 2^32)
      if !accepted then
        outside := outside + 1
        continue
      let result := h.call entry.store index entry.args
      if result.gas != op h units then throw (IO.userError s!"f{index} exact gas mismatch")
      if index == 568 || index == 570 || index == 576 then
        let expected := if index == 568 then (a.toNat+b.toNat-1)/b.toNat else
          if index == 570 then (a.toNat+3)/4 else (DeallocateListSize.endWord memory a).toNat-a.toNat-8
        if returnsU32 result != some expected then throw (IO.userError s!"f{index} result mismatch")
        checkMemory h index result.after memory
      else
        match result.ending with
        | .returned [] => pure ()
        | _ => throw (IO.userError s!"f{index} did not return void")
        let expected := if index == 575 then DeallocateListState.finalMemory q else finalMemory core
        checkMemory h index result.after expected
      if h.stackPointer result.after != h.stackPointer entry.store ||
          result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
          result.after.host.returnData != entry.store.host.returnData ||
          result.after.host.returnedPromise != entry.store.host.returnedPromise then
        throw (IO.userError s!"f{index} SP/functional host frame mismatch")
      checkFuel h index fuel entry
      if index == 68 && method == "ft_total_supply" then getterDrops := getterDrops + 1
      checked := checked + 1
    if checked == 0 then throw (IO.userError s!"no accepted f{index} captures")
    IO.println s!"PASS f{index}: {checked} accepted captures; exact {units} units/{fuel} steps and sequential memory; {outside} outside contract"
  if getterDrops != 2 then throw (IO.userError s!"expected exactly two accepted getter drops, got {getterDrops}")
  IO.println "PASS both explicit ft_total_supply vector-drop sites satisfy the accepted heap conditions"
#eval validate
end WNear.Proofs.DeallocateValidation
