import Proofs.StateDecodeRawState
import Proofs.AllocateLayoutWrapperFootprint

/-! The actual752 stack writes preserve the original directly-fitting heap
conditions. No post-layout allocation-domain premise is assumed. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 laidOutMemory AllocateLayoutWrapper.finalMemory

theorem stack_numbers (p : Layout) (hn : Native p) :
    (scratch p).toNat=p.spRaw.toNat-32 ∧
    (scratch769 p).toNat=p.spRaw.toNat-48 ∧
    (AllocateLayoutWrapper.scratch (layout752 p)).toNat=p.spRaw.toNat-48 ∧
    (layout752 p).out.toNat=p.spRaw.toNat-8 ∧
    (AllocatePositive.scratch p.toPositive).toNat=p.spRaw.toNat-64 ∧
    (AllocatePositive.scratch p.toPositive+12).toNat=(AllocatePositive.scratch p.toPositive).toNat+12 := by
  have lo:=hn.spLower
  have hi:=p.spRaw.toNat_lt
  have a : (scratch p).toNat=p.spRaw.toNat-32 := by
    rw [scratch,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have b : (scratch769 p).toNat=p.spRaw.toNat-48 := by
    rw [scratch769,UInt32.toNat_sub,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have c : p.sp.toNat=p.spRaw.toNat-48 := by
    rw [hn.childSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have d : (layout752 p).out.toNat=p.spRaw.toNat-8 := by
    change (scratch p+24).toNat=_
    rw [UInt32.toNat_add,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have e : (AllocatePositive.scratch p.toPositive).toNat=p.spRaw.toNat-64 := by
    change (p.sp-16).toNat=_
    rw [UInt32.toNat_sub,c]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨a,b,b,d,e,(AllocatePositive.scratch_numbers p.toPositive hn.allocation).2.1⟩

theorem layout_bounds (p : Layout) (hn : Native p) :
    (AllocateLayoutWrapper.scratch (layout752 p)).toNat+16≤p.memory.byteSize ∧
    (layout752 p).out.toNat+8≤p.memory.byteSize := by
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have hi:=hn.spBound
  rw [n.2.2.1,n.2.2.2.1]
  omega

theorem layout_spec (p : Layout) (hn : Native p) :
    (laidOutMemory p).wf ∧ (laidOutMemory p).byteSize=p.memory.byteSize ∧ (laidOutMemory p).max=p.memory.max := by
  have b:=layout_bounds p hn
  have s:=AllocateLayoutWrapper.final_footprint (layout752 p) hn.allocation.wf b.1 b.2
  unfold laidOutMemory
  exact ⟨s.1,s.2.1,s.2.2.1⟩

theorem layout_word (p : Layout) (hn : Native p) (address : Nat) (ha : p.spRaw.toNat≤address) :
    readI32 (laidOutMemory p) address=readI32 p.memory address := by
  have b:=layout_bounds p hn
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  unfold laidOutMemory
  apply AllocateLayoutWrapper.final_word_frame (layout752 p) hn.allocation.wf b.1 b.2 address
  · right;rw [n.2.2.1];omega
  · right;rw [n.2.2.2.1];omega

def originalSaved (p : Layout) := AllocatePositive.savedMemory p.toPositive
def actualSaved (p : Layout) := AllocatePositive.savedMemory (actualPositive p)

theorem originalSaved_spec (p : Layout) (hn : Native p) :
    (originalSaved p).wf ∧ (originalSaved p).byteSize=p.memory.byteSize := by
  have b:=AllocatePositive.scratch_numbers p.toPositive hn.allocation
  have s:=writeI32_spec p.memory ((AllocatePositive.scratch p.toPositive).toNat+12)
    (readI32 p.memory p.allocator.toNat) hn.allocation.wf (by omega)
  exact ⟨s.1,s.2.1⟩
theorem actualSaved_spec (p : Layout) (hn : Native p) :
    (actualSaved p).wf ∧ (actualSaved p).byteSize=p.memory.byteSize := by
  have ls:=layout_spec p hn
  have b:=AllocatePositive.scratch_numbers p.toPositive hn.allocation
  have bound : (AllocatePositive.scratch p.toPositive).toNat+12+4≤(laidOutMemory p).byteSize := by rw [ls.2.1];omega
  have s:=writeI32_spec (laidOutMemory p) ((AllocatePositive.scratch p.toPositive).toNat+12)
    (readI32 (laidOutMemory p) p.allocator.toNat) ls.1 bound
  exact ⟨s.1,s.2.1.trans ls.2.1⟩

theorem saved_word (p : Layout) (hn : Native p) (address : Nat) (ha : p.spRaw.toNat≤address) :
    readI32 (actualSaved p) address=readI32 (originalSaved p) address := by
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have ls:=layout_spec p hn
  have b:=AllocatePositive.scratch_numbers p.toPositive hn.allocation
  have bound : (AllocatePositive.scratch p.toPositive).toNat+12+4≤(laidOutMemory p).byteSize := by rw [ls.2.1];omega
  have newRead:=PanicAllocateReadback.read_write_frame (laidOutMemory p) address
    ((AllocatePositive.scratch p.toPositive).toNat+12) (readI32 (laidOutMemory p) p.allocator.toNat) ls.1 bound
    (Or.inr (by rw [n.2.2.2.2.1];omega))
  have oldRead:=PanicAllocateReadback.read_write_frame p.memory address
    ((AllocatePositive.scratch p.toPositive).toNat+12) (readI32 p.memory p.allocator.toNat) hn.allocation.wf (by omega)
    (Or.inr (by rw [n.2.2.2.2.1];omega))
  exact newRead.trans ((layout_word p hn address ha).trans oldRead.symm)

theorem saved_head (p : Layout) (hn : Native p) :
    AllocateSearch.head (AllocatePositive.searchLayout (actualPositive p))=
      AllocateSearch.head (AllocatePositive.searchLayout p.toPositive) := by
  have n:=stack_numbers p hn
  have ls:=layout_spec p hn
  have b:=AllocatePositive.scratch_numbers p.toPositive hn.allocation
  have bound : (AllocatePositive.scratch p.toPositive).toNat+12+4≤(laidOutMemory p).byteSize := by rw [ls.2.1];omega
  have newRead:=PanicAllocateReadback.read_write_self (laidOutMemory p)
    ((AllocatePositive.scratch p.toPositive).toNat+12) (readI32 (laidOutMemory p) p.allocator.toNat) ls.1 bound
  have oldRead:=PanicAllocateReadback.read_write_self p.memory
    ((AllocatePositive.scratch p.toPositive).toNat+12) (readI32 p.memory p.allocator.toNat) hn.allocation.wf (by omega)
  change readI32 (actualSaved p) (AllocatePositive.scratch p.toPositive+12).toNat=
    readI32 (originalSaved p) (AllocatePositive.scratch p.toPositive+12).toNat
  rw [n.2.2.2.2.2]
  exact newRead.trans ((layout_word p hn p.allocator.toNat hn.heapAbove).trans oldRead.symm)

theorem search_native (p : Layout) (hn : Native p) :
    AllocateSearch.Native (AllocatePositive.searchLayout (actualPositive p)) := by
  let old:=AllocatePositive.searchLayout p.toPositive
  let next:=AllocatePositive.searchLayout (actualPositive p)
  have original : AllocateSearch.Native old:=hn.allocation.search
  have actualShape:=actualSaved_spec p hn
  have originalShape:=originalSaved_spec p hn
  have headEq : AllocateSearch.head next=AllocateSearch.head old:=saved_head p hn
  have headerRead : readI32 (actualSaved p) (AllocateSearch.head old).toNat=
      readI32 (originalSaved p) (AllocateSearch.head old).toNat := saved_word p hn _ hn.headAbove
  have flagRead : readI32 (actualSaved p) ((AllocateSearch.head old).toNat+8)=
      readI32 (originalSaved p) ((AllocateSearch.head old).toNat+8) := saved_word p hn _ (by have h : p.spRaw.toNat≤(AllocateSearch.head old).toNat:=hn.headAbove;omega)
  have finishEq : Allocate.endWord (actualSaved p) (AllocateSearch.head old)=
      Allocate.endWord (originalSaved p) (AllocateSearch.head old) := by
    unfold Allocate.endWord
    rw [headerRead]
  have rootBound : next.root.toNat+4≤next.memory.byteSize := by
    change old.root.toNat+4≤(actualSaved p).byteSize
    rw [actualShape.2,←originalShape.2]
    exact original.rootBound
  have split : Allocate.SplitNative next.memory (AllocateSearch.head next) next.words := by
    change Allocate.SplitNative (actualSaved p) (AllocateSearch.head next) old.words
    rw [headEq]
    refine ⟨original.split.wordsPositive,?_,?_⟩
    · rw [finishEq]
      exact original.split.room
    · rw [finishEq,actualShape.2,←originalShape.2]
      exact original.split.endBound
  refine ⟨actualShape.1,rootBound,?_,split,?_,?_,?_,?_⟩
  · rw [headEq];exact original.headNonzero
  · change (Allocate.endWord (actualSaved p) (AllocateSearch.head next)).toNat+8≤(actualSaved p).byteSize
    rw [headEq,finishEq,actualShape.2,←originalShape.2]
    exact original.endBound
  · change readI32 (actualSaved p) (AllocateSearch.head next).toNat &&& 3=0
    rw [headEq,headerRead]
    exact original.headFlags
  · change readI32 (actualSaved p) ((AllocateSearch.head next).toNat+8) &&& 1=0
    rw [headEq,flagRead]
    exact original.candidateFlag
  · change old.vtable.toNat+20≤(actualSaved p).byteSize
    rw [actualShape.2,←originalShape.2]
    exact original.vtableBound

/-- Full actual direct allocation domain, reconstructed after752 solely from
original heap conditions and separation of the original stack and heap. -/
theorem allocation_native (p : Layout) (hn : Native p) : AllocatePositive.Native (actualPositive p) := by
  have shape:=layout_spec p hn
  refine ⟨hn.allocation.positive,hn.allocation.rounding,shape.1,?_,hn.allocation.spLower,?_,?_,search_native p hn⟩
  · change (laidOutMemory p).byteSize≤2^32
    rw [shape.2.1];exact hn.allocation.width
  · change p.sp.toNat≤(laidOutMemory p).byteSize
    rw [shape.2.1];exact hn.allocation.spBound
  · change p.allocator.toNat+4≤(laidOutMemory p).byteSize
    rw [shape.2.1];exact hn.allocation.allocatorBound

/-- The indirect callback selector is also read from the real post-layout saved
memory; it equals the original selector by the same stack footprint. -/
theorem callback_word (p : Layout) (hn : Native p) :
    readI32 (actualSaved p) (1057464+16)=readI32 (originalSaved p) (1057464+16) :=
  saved_word p hn _ (by have h:=hn.callbackAbove;omega)

end WNear.Proofs.StateDecodeRaw
