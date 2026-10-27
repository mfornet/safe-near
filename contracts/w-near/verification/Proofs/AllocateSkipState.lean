import Proofs.AllocateSearchCall
import NearVM.MemoryListWordRules
import Proofs.ValueReturnOuterLayout

/-! Original heap conditions for skipping one short node before the direct split. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid)

abbrev Layout := AllocateSearch.Layout

def next (p : Layout) := readI32 p.memory ((head p).toNat+8)
def nextMemory (p : Layout) := writeI32 p.memory p.root.toNat (next p)
def nextLayout (p : Layout) : Layout := {p with memory:=nextMemory p}

structure Native (p : Layout) : Prop where
  wf : p.memory.wf
  rootBound : p.root.toNat+4≤p.memory.byteSize
  headNonzero : head p≠0
  headBound : (head p).toNat+12≤p.memory.byteSize
  candidateFlag : next p &&& 1=0
  firstNormal : (head p).toNat+8≤(DeallocateListSize.endWord p.memory (head p)).toNat
  short : (DeallocateListSize.size p.memory (head p)).toNat<p.words.toNat*4
  nextNonzero : next p≠0
  split : Allocate.SplitNative p.memory (next p) p.words
  endBound : (Allocate.endWord p.memory (next p)).toNat+8≤p.memory.byteSize
  headFlags : readI32 p.memory (next p).toNat &&& 3=0
  nextCandidateFlag : readI32 p.memory ((next p).toNat+8) &&& 1=0
  vtableBound : p.vtable.toNat+20≤p.memory.byteSize
  rootNextSep : p.root.toNat+4≤(next p).toNat ∨ (next p).toNat+12≤p.root.toNat
  rootVtableSep : p.root.toNat+4≤p.vtable.toNat+16 ∨ p.vtable.toNat+20≤p.root.toNat

def advanced (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (candidateAfter s op) op 5) p.memoryIndex p.root.toNat p.memory (next p)
def hopped (s : Store NearState) (op : Nat) (p : Layout) := chargedStore (advanced s op p) (2*op)
def resumed (s : Store NearState) (op : Nat) (p : Layout) := paid (hopped s op p) op 4
def hopFrame (frame : CallFrame) (p : Layout) :=
  {candidateFrame frame p with locals:=(candidateFrame frame p).locals.set! 1 (.i32 (next p))}

end WNear.Proofs.AllocateSkip
