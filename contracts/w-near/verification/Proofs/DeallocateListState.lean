import Proofs.DeallocateListWrite

/-! Exact sequential states of the captured two-link f575 unlink path. -/
namespace WNear.Proofs.DeallocateListState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  memoryIndex : Nat
  pointer : UInt32
  memory : Memory

def firstRaw (p : Layout) := readI32 p.memory p.pointer.toNat
def firstLink (p : Layout) := firstRaw p &&& 4294967292

def firstMemory (p : Layout) := writeI32 p.memory ((firstLink p).toNat + 4)
  (DeallocateListWrite.merged p.memory ((firstLink p).toNat + 4) (p.pointer.toNat + 4))
def firstStore (s : Store NearState) (op : Nat) (p : Layout) :=
  DeallocateListWrite.writeStore (paid s op 17) op p.memoryIndex 4 4 (firstLink p) p.pointer p.memory

def secondRaw (p : Layout) := readI32 (firstMemory p) (p.pointer.toNat + 4)
def secondLink (p : Layout) := secondRaw p &&& 4294967292

def secondMemory (p : Layout) := writeI32 (firstMemory p) (secondLink p).toNat
  (DeallocateListWrite.merged (firstMemory p) (secondLink p).toNat p.pointer.toNat)
def secondStore (s : Store NearState) (op : Nat) (p : Layout) :=
  DeallocateListWrite.writeStore (paid (firstStore s op p) op 8) op p.memoryIndex 0 0
    (secondLink p) p.pointer (firstMemory p)
def finalRaw (p : Layout) := readI32 (secondMemory p) (p.pointer.toNat + 4)
def secondAfter (s : Store NearState) (op : Nat) (p : Layout) := paid (secondStore s op p) op 3

def firstFrame (frame : CallFrame) (p : Layout) :=
  DeallocateListGuards.selectedFrame (DeallocateListGuards.headerFrame frame (firstRaw p)) (firstLink p)
def secondFrame (frame : CallFrame) (p : Layout) := DeallocateListGuards.headerFrame (firstFrame frame p) (secondRaw p)
def finalFrame (frame : CallFrame) (p : Layout) :=
  {secondFrame frame p with locals := (secondFrame frame p).locals.set! 1 (.i32 (finalRaw p))}

structure Ready (s : Store NearState) (frame : CallFrame) (p : Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  pointer : frame.locals[0]? = some (.i32 p.pointer)
  locals : 3 ≤ frame.locals.size
  wf : p.memory.wf
  nodeBound : p.pointer.toNat + 8 ≤ p.memory.byteSize
  firstNonzero : firstLink p ≠ 0
  firstFlag : firstRaw p &&& 2 = 0
  firstBound : (firstLink p).toNat + 8 ≤ p.memory.byteSize
  secondNonzero : secondLink p ≠ 0
  secondBound : (secondLink p).toNat + 4 ≤ (firstMemory p).byteSize

end WNear.Proofs.DeallocateListState
