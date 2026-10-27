import Proofs.DeallocateCalls
import Proofs.DeallocateListFrame

/-! Sequential state and original native conditions for the captured previous-free
coalescing path of actual f582. No execution outcome occurs among the premises. -/
namespace WNear.Proofs.DeallocateCore
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

structure Layout where
  mi : ModuleInst
  memoryIndex : Nat
  allocator : UInt32
  pointer : UInt32
  length : UInt32
  alignment : UInt32
  header : UInt32
  previousAddress : UInt32
  previous : UInt32
  memory : Memory
  address568 : Nat
  address570 : Nat
  address575 : Nat
  address576 : Nat

def oldHead (p : Layout) := readI32 p.memory p.allocator.toNat
def markedMemory (p : Layout) := writeI32 p.memory p.header.toNat (readI32 p.memory p.header.toNat &&& 4294967294)
def zeroMemory (p : Layout) := writeI32 (markedMemory p) p.pointer.toNat 0
def unlinkLayout (p : Layout) : DeallocateListState.Layout :=
  {mi := p.mi,memoryIndex := p.memoryIndex,pointer := p.header,memory := zeroMemory p}
def unlinkedMemory (p : Layout) := DeallocateListState.finalMemory (unlinkLayout p)
def finalMemory (p : Layout) := writeI32 (unlinkedMemory p) p.allocator.toNat (oldHead p)

def guarded (s : Store NearState) (op : Nat) := paid s op 6
def aligned (s : Store NearState) (op : Nat) := Deallocate.aligned (guarded s op) op
def saved (s : Store NearState) (op : Nat) := paid (aligned s op) op 3
def marked (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (saved s op) op 9) p.memoryIndex p.header.toNat p.memory (readI32 p.memory p.header.toNat &&& 4294967294)
def sized (s : Store NearState) (op : Nat) (p : Layout) := Deallocate.sized (marked s op p) op
def zeroed (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (sized s op p) op 3) p.memoryIndex p.pointer.toNat (markedMemory p) 0
def previousSelected (s : Store NearState) (op : Nat) (p : Layout) := paid (zeroed s op p) op 15
def unlinkEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def unlinked (s : Store NearState) (op : Nat) (p : Layout) :=
  DeallocateListState.after (unlinkEntered (paid (previousSelected s op p) op 1) op) op (unlinkLayout p)
def flagChecked (s : Store NearState) (op : Nat) (p : Layout) := paid (unlinked s op p) op 6
def previousSized (s : Store NearState) (op : Nat) (p : Layout) := Deallocate.sized (flagChecked s op p) op
def restored (s : Store NearState) (op : Nat) (p : Layout) := paid (previousSized s op p) op 3
def after (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (restored s op p) op 3) p.memoryIndex p.allocator.toNat (unlinkedMemory p) (oldHead p)
def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (12 * op)
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  module : s.modules[inst]? = some p.mi
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  index568 : p.mi.funcAddrs[568]? = some p.address568
  function568 : s.funcs[p.address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 inst WNear.Binary.DeallocateAlign.function568)
  index570 : p.mi.funcAddrs[570]? = some p.address570
  function570 : s.funcs[p.address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 inst WNear.Binary.DeallocateAlign.function570)
  index575 : p.mi.funcAddrs[575]? = some p.address575
  function575 : s.funcs[p.address575]? = some (.wasm WNear.Binary.DeallocateList.unlinkSignature inst WNear.Binary.DeallocateList.unlinkFunction)
  index576 : p.mi.funcAddrs[576]? = some p.address576
  function576 : s.funcs[p.address576]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature inst WNear.Binary.DeallocateList.sizeFunction)

/-- Pure conditions on the actual sequential memory snapshots. Bounds and reads
are explicit even when allocator records alias each other. -/
structure Native (p : Layout) : Prop where
  wf : p.memory.wf
  pointerNonzero : p.pointer ≠ 0
  lengthNonzero : p.length ≠ 0
  lengthBound : p.length.toNat + 4 < 2 ^ 32
  headerEq : p.pointer + 4294967288 = p.header
  previousAddressEq : p.pointer + 4294967292 = p.previousAddress
  allocatorBound : p.allocator.toNat + 4 ≤ p.memory.byteSize
  headerBound : p.header.toNat + 4 ≤ p.memory.byteSize
  pointerBound : p.pointer.toNat + 4 ≤ p.memory.byteSize
  currentSize : p.header.toNat + 8 ≤ (DeallocateListSize.endWord (markedMemory p) p.header).toNat
  previousAddressBound : p.previousAddress.toNat + 4 ≤ (zeroMemory p).byteSize
  previousRead : Deallocate.previous (zeroMemory p) p.previousAddress = p.previous
  previousNonzero : p.previous ≠ 0
  previousBound : p.previous.toNat + 1 ≤ (zeroMemory p).byteSize
  previousFree : readByteWord (zeroMemory p) p.previous.toNat &&& 1 = 0
  firstNonzero : DeallocateListState.firstLink (unlinkLayout p) ≠ 0
  firstFlag : DeallocateListState.firstRaw (unlinkLayout p) &&& 2 = 0
  firstBound : (DeallocateListState.firstLink (unlinkLayout p)).toNat + 8 ≤ (zeroMemory p).byteSize
  nodeBound : p.header.toNat + 8 ≤ (zeroMemory p).byteSize
  secondNonzero : DeallocateListState.secondLink (unlinkLayout p) ≠ 0
  secondBound : (DeallocateListState.secondLink (unlinkLayout p)).toNat + 4 ≤ (DeallocateListState.firstMemory (unlinkLayout p)).byteSize
  unlinkedHeaderBound : p.header.toNat + 1 ≤ (unlinkedMemory p).byteSize
  unlinkedFlag : readByteWord (unlinkedMemory p) p.header.toNat &&& 2 = 0
  unlinkedPreviousBound : p.previous.toNat + 4 ≤ (unlinkedMemory p).byteSize
  previousSize : p.previous.toNat + 8 ≤ (DeallocateListSize.endWord (unlinkedMemory p) p.previous).toNat
  finalAllocatorBound : p.allocator.toNat + 4 ≤ (unlinkedMemory p).byteSize

structure Ready (s : Store NearState) (frame : CallFrame) (p : Layout) : Prop where
  code : Code s frame.inst p
  memory : s.mems[p.memoryIndex]? = some p.memory
  allocator : frame.locals[0]? = some (.i32 p.allocator)
  pointer : frame.locals[1]? = some (.i32 p.pointer)
  length : frame.locals[2]? = some (.i32 p.length)
  alignment : frame.locals[3]? = some (.i32 p.alignment)
  locals : 7 ≤ frame.locals.size
  native : Native p

end WNear.Proofs.DeallocateCore
