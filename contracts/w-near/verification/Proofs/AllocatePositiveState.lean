import Binary.AllocatePositive
import Proofs.AllocatePrefix
import Proofs.AllocateSearchCall
import Proofs.ValueReturnBorrow

/-! Original resources and exact sequential states of581's positive fitting path. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)

structure Layout where
  mi : ModuleInst
  memoryIndex : Nat
  globalIndex : Nat
  global : GlobalInst
  memory : Memory
  allocator : UInt32
  size : UInt32
  sp : UInt32
  tableAddress : Nat
  table : TableInst
  callbackAddress : Nat
  callbackInst : Nat
  unitsAddress : Nat
  minimumAddress : Nat
  sizeAddress : Nat
  alignAddress : Nat
  roundAddress : Nat
  searchAddress : Nat

def scratch (p : Layout) := p.sp-16
def words (p : Layout) := DeallocateAlign.quotient p.size 4
def savedMemory (p : Layout) := writeI32 p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat)
def searchLayout (p : Layout) : AllocateSearch.Layout :=
  {mi:=p.mi,memoryIndex:=p.memoryIndex,tableAddress:=p.tableAddress,table:=p.table,
   words:=words p,root:=scratch p+12,context:=1057464,vtable:=1057464,memory:=savedMemory p,
   callbackAddress:=p.callbackAddress,callbackInst:=p.callbackInst,unitsAddress:=p.unitsAddress,
   minimumAddress:=p.minimumAddress,sizeAddress:=p.sizeAddress}
def result (p : Layout) := AllocateSearch.pointer (searchLayout p)
def searchedMemory (p : Layout) := AllocateSearch.finalMemory (searchLayout p)
def finalMemory (p : Layout) := writeI32 (searchedMemory p) p.allocator.toNat
  (readI32 (searchedMemory p) ((scratch p).toNat+12))

def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 3 (.i32 (scratch p))}
def prefixed (s : Store NearState) (op : Nat) (p : Layout) :=
  Allocate.prefixAfter (paid (reserved s op p) op 2) op p.memoryIndex (scratch p) p.allocator p.memory
def prefixFrame (frame : CallFrame) (p : Layout) := Allocate.roundedFrame (reservedFrame frame p) p.size
def searched (s : Store NearState) (op : Nat) (p : Layout) := AllocateSearch.callAfter (paid (prefixed s op p) op 7) op (searchLayout p)
def found (s : Store NearState) (op : Nat) (p : Layout) := paid (searched s op p) op 2
def resultFrame (frame : CallFrame) (p : Layout) := {prefixFrame frame p with locals:=(prefixFrame frame p).locals.set! 1 (.i32 (result p))}
def updated (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (found s op p) op 4) p.memoryIndex p.allocator.toNat (searchedMemory p)
    (readI32 (searchedMemory p) ((scratch p).toNat+12))
def after (s : Store NearState) (op : Nat) (p : Layout) := paid (setGlobal (paid (updated s op p) op 4) p.globalIndex (.i32 p.sp)) op 1

structure Native (p : Layout) : Prop where
  positive : p.size≠0
  rounding : p.size.toNat+4<2^32
  wf : p.memory.wf
  width : p.memory.byteSize≤2^32
  spLower : 16≤p.sp.toNat
  spBound : p.sp.toNat≤p.memory.byteSize
  allocatorBound : p.allocator.toNat+4≤p.memory.byteSize
  search : AllocateSearch.Native (searchLayout p)

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  search : AllocateSearch.SearchCode s (searchLayout p) inst
  globalIndex : p.mi.globalAddrs[0]?=some p.globalIndex
  alignIndex : p.mi.funcAddrs[568]?=some p.alignAddress
  alignFunction : s.funcs[p.alignAddress]?=some (.wasm WNear.Binary.DeallocateAlign.signature568 inst WNear.Binary.DeallocateAlign.function568)
  roundIndex : p.mi.funcAddrs[570]?=some p.roundAddress
  roundFunction : s.funcs[p.roundAddress]?=some (.wasm WNear.Binary.DeallocateAlign.signature570 inst WNear.Binary.DeallocateAlign.function570)
  searchIndex : p.mi.funcAddrs[580]?=some p.searchAddress
  searchFunction : s.funcs[p.searchAddress]?=some (.wasm WNear.Binary.AllocateSearch.signature inst WNear.Binary.Allocate.searchFunction)

theorem scratch_numbers (p : Layout) (hn : Native p) :
    (scratch p).toNat=p.sp.toNat-16 ∧ (scratch p+12).toNat=(scratch p).toNat+12 ∧
    (scratch p).toNat+16≤p.memory.byteSize ∧ scratch p+16=p.sp := by
  have spLt := p.sp.toNat_lt
  have spLower := hn.spLower
  have spBound := hn.spBound
  have width := hn.width
  have first : (scratch p).toNat=p.sp.toNat-16 := by
    rw [scratch,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  refine ⟨first,?_,by omega,UInt32.sub_add_cancel p.sp 16⟩
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega
end WNear.Proofs.AllocatePositive
