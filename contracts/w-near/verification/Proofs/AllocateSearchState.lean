import Proofs.AllocateSplit
import Proofs.AllocateLinks
import Proofs.AllocateNative
import Proofs.AllocateCallback
import Proofs.AllocateArithmeticBody

/-! Pure original-heap layout and sequential states for f580's direct split.
This module contains no assumed execution or post-allocation lookup. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open Allocate
open StorePairCaller (paid)

structure Layout where
  mi : ModuleInst
  memoryIndex : Nat
  tableAddress : Nat
  table : TableInst
  words : UInt32
  root : UInt32
  context : UInt32
  vtable : UInt32
  memory : Memory
  callbackAddress : Nat
  callbackInst : Nat
  unitsAddress : Nat
  minimumAddress : Nat
  sizeAddress : Nat

def head (p : Layout) := readI32 p.memory p.root.toNat
def header (p : Layout) := splitHeader p.memory (head p) p.words
def finish (p : Layout) := endWord p.memory (head p)
def pointer (p : Layout) := splitPointer p.memory (head p) p.words

def clearedMemory (p : Layout) := Allocate.clearedMemory p.memory (header p)
def initializedMemory (p : Layout) := writeI32 (clearedMemory p) (header p).toNat
  (readI32 (clearedMemory p) (head p).toNat &&& 4294967292)
def backlinkedMemory (p : Layout) := writeI32 (initializedMemory p) ((finish p).toNat+4)
  (taggedValue (initializedMemory p) (finish p) 4 (header p))
def previousMemory (p : Layout) := writeI32 (backlinkedMemory p) ((header p).toNat+4)
  (taggedValue (backlinkedMemory p) (header p) 4 (head p))
def unflaggedMemory (p : Layout) := writeI32 (previousMemory p) ((head p).toNat+8)
  (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294)
def linkedMemory (p : Layout) := writeI32 (unflaggedMemory p) (head p).toNat
  (taggedValue (unflaggedMemory p) (head p) 0 (header p))
def finalMemory (p : Layout) := Allocate.markedMemory (linkedMemory p) (header p)

structure Native (p : Layout) : Prop where
  memoryWf : p.memory.wf
  rootBound : p.root.toNat+4 ≤ p.memory.byteSize
  headNonzero : head p ≠ 0
  split : SplitNative p.memory (head p) p.words
  endBound : (finish p).toNat+8 ≤ p.memory.byteSize
  headFlags : readI32 p.memory (head p).toNat &&& 3 = 0
  candidateFlag : readI32 p.memory ((head p).toNat+8) &&& 1 = 0
  vtableBound : p.vtable.toNat+20 ≤ p.memory.byteSize

end WNear.Proofs.AllocateSearch
