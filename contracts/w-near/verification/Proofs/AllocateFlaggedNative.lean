import Proofs.AllocateLoopCandidate
import Proofs.AllocateSearchFitPrefix

/-! Actual flags-two original-heap premise for580. This does not assert the
flags-zero Native predicate used by the earlier direct-fit proof. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch

abbrev head := AllocateSearch.head
abbrev header := AllocateSearch.header
abbrev finish := AllocateSearch.finish
abbrev pointer := AllocateSearch.pointer

structure Native (p : Layout) : Prop where
  memoryWf : p.memory.wf
  rootBound : p.root.toNat+4≤p.memory.byteSize
  headNonzero : head p≠0
  split : Allocate.SplitNative p.memory (head p) p.words
  endBound : (finish p).toNat≤p.memory.byteSize
  headFlags : readI32 p.memory (head p).toNat &&& 3 = 2
  candidateFlag : readI32 p.memory ((head p).toNat+8) &&& 1 = 0
  vtableBound : p.vtable.toNat+20≤p.memory.byteSize

theorem intervals (p : Layout) (hn : Native p) :
    (head p).toNat+72≤(header p).toNat ∧ (header p).toNat+12≤(finish p).toNat ∧
    (finish p).toNat≤p.memory.byteSize := by
  have ptr := Allocate.split_pointer_toNat p.memory (head p) p.words hn.split
  have hdr := Allocate.split_header_toNat p.memory (head p) p.words hn.split
  have room := hn.split.room
  have positive := hn.split.wordsPositive
  change (head p).toNat+72≤(Allocate.splitHeader p.memory (head p) p.words).toNat ∧ _
  change _ ∧ (Allocate.splitHeader p.memory (head p) p.words).toNat+12≤
    (Allocate.endWord p.memory (head p)).toNat ∧ _
  exact ⟨by omega,by omega,hn.endBound⟩
end WNear.Proofs.AllocateFlagged
