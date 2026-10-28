import Proofs.AllocateRawForwardDirectResult
import Proofs.AllocateLayoutWrapperResult

/-! Original-memory data for767's positive, flag-zero, directly-fitting path.
Every later heap and stack memory is a pure sequential expression. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic

structure Layout extends toPositive : AllocatePositive.Layout where
  spRaw : UInt32
  globalRaw : GlobalInst
  outRaw : UInt32
  flag : UInt32
  address751 : Nat
  address752 : Nat
  address769 : Nat
  address770 : Nat
  address310 : Nat

def scratch (p : Layout) := p.spRaw-32
def scratch769 (p : Layout) := scratch p-16

def layout752 (p : Layout) : AllocateLayoutWrapper.Layout :=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,
   global:={p.globalRaw with value:=.i32 (scratch p)},sp:=scratch p,
   out:=scratch p+24,size:=p.size,memory:=p.memory,
   calleeIndex:=751,calleeAddress:=p.address751,message:=1065620,location:=1065664,previous:=1065508}
def laidOutMemory (p : Layout) := AllocateLayoutWrapper.finalMemory (layout752 p)
def actualPositive (p : Layout) : AllocatePositive.Layout := {p.toPositive with memory:=laidOutMemory p}
def result (p : Layout) := AllocatePositive.result (actualPositive p)
def allocatedMemory (p : Layout) := AllocatePositive.finalMemory (actualPositive p)
def out770 (p : Layout) := scratch769 p+8
--770 writes the length first and then the returned allocation pointer.
def highMemory770 (p : Layout) := writeI32 (allocatedMemory p) ((out770 p).toNat+4) p.size
def memory770 (p : Layout) := writeI32 (highMemory770 p) (out770 p).toNat (result p)
--769 performs two separate loads, with its low output store between them.
def lowMemory769 (p : Layout) := writeI32 (memory770 p) (scratch p+16).toNat (readI32 (memory770 p) (out770 p).toNat)
def memory769 (p : Layout) := writeI32 (lowMemory769 p) ((scratch p+16).toNat+4)
  (readI32 (lowMemory769 p) ((out770 p).toNat+4))
--767 caches both output words before either caller-output store.
def cachedPointer (p : Layout) := readI32 (memory769 p) (scratch p+16).toNat
def cachedLength (p : Layout) := readI32 (memory769 p) ((scratch p).toNat+20)
def finalMemory (p : Layout) := writeI32 (writeI32 (memory769 p) p.outRaw.toNat (cachedPointer p))
  (p.outRaw.toNat+4) (cachedLength p)

structure Native (p : Layout) : Prop where
  allocation : AllocatePositive.Native p.toPositive
  childSP : p.sp=p.spRaw-48
  childGlobal : p.global={p.globalRaw with value:=.i32 p.sp}
  spLower : 64≤p.spRaw.toNat
  spBound : p.spRaw.toNat≤p.memory.byteSize
  outBound : p.outRaw.toNat+8≤p.memory.byteSize
  flagZero : p.flag=0
  sizeSigned : p.size.toNat<2^31
  heapAbove : p.spRaw.toNat≤p.allocator.toNat
  headAbove : p.spRaw.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat
  callbackAbove : p.spRaw.toNat≤1057464

end WNear.Proofs.StateDecodeRaw
