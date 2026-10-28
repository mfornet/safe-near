import Proofs.AllocateRecordCopyState
import Proofs.AllocateLayoutWrapperCall
import Proofs.AllocateSetupGrowth

/-! Original-data layout for686. The child allocation template describes original
memory; actualRecord replaces it by the real685 post-memory and a pure grown witness. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toRecord : AllocateRecord.Layout where
  outerSP : UInt32
  outerGlobal : GlobalInst
  out686 : UInt32
  address684 : Nat
  address685 : Nat
  address689 : Nat
  address690 : Nat

def reservedSP (p : Layout) := p.outerSP-32

def layout685 (p : Layout) : AllocateLayoutWrapper.Layout :=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,
   global:={p.outerGlobal with value:=.i32 (reservedSP p)},sp:=reservedSP p,
   out:=reservedSP p+24,size:=p.size,memory:=p.memory,
   calleeIndex:=684,calleeAddress:=p.address684,message:=1063100,location:=1063144,previous:=1063084}

def laidOutMemory (p : Layout) := AllocateLayoutWrapper.finalMemory (layout685 p)
def targetSaved (p : Layout) := writeI32 (laidOutMemory p) ((p.sp-16).toNat+12)
  (readI32 (laidOutMemory p) p.allocator.toNat)
def delta (p : Layout) := AllocateGrowth.delta (AllocateRetry.growthLayout p.toRecord.toZeroed.toRetry)
def derivedGrown (p : Layout) : Memory :=
  {targetSaved p with pages:=(targetSaved p).pages ++ Array.replicate (delta p).toNat ByteArray.empty}
def actualRecord (p : Layout) : AllocateRecord.Layout :=
  {p.toRecord with memory:=laidOutMemory p,grown:=derivedGrown p}
def layout690 (p : Layout) : AllocateRecordCopy.Layout :=
  {inner:=actualRecord p,out:=reservedSP p+8,sp:=reservedSP p,
   global:={p.outerGlobal with value:=.i32 (reservedSP p)},address689:=p.address689}

structure Native (p : Layout) : Prop where
  allocation : AllocateZeroedRetry.Native p.toRecord.toZeroed
  childSP : p.sp=p.outerSP-48
  childOut : p.out=p.sp+8
  childGlobal : p.global={p.outerGlobal with value:=.i32 p.sp}
  spLower : 64≤p.outerSP.toNat
  spBound : p.outerSP.toNat≤p.memory.byteSize
  sizeBound : p.size.toNat<2^31
  outputBound : p.out686.toNat+8≤p.memory.byteSize
  heapAbove : p.outerSP.toNat≤p.allocator.toNat
  callbackAbove : p.outerSP.toNat≤1057464+16

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (reservedSP p))
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 4
def laidOut (s : Store NearState) (op : Nat) (p : Layout) :=
  AllocateLayoutWrapper.called (arguments s op p) op (layout685 p)
end WNear.Proofs.AllocateVector
