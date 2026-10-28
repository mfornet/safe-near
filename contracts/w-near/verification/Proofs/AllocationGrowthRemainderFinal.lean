import Proofs.AllocationGrowthRemainderRetry
import Proofs.AllocateFlaggedOldFrame

/-! The actual final allocator-root store retains the free remainder and names
its head. Every input hypothesis is on the original growth invocation. -/
namespace WNear.Proofs.AllocationGrowthRemainder
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

 theorem retry_saved_head(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    readI32 (AllocateRetry.searchedMemory p) ((AllocateRetry.scratch p).toNat+12)=
      AllocateFlagged.head (AllocateRetry.secondLayout p):=by
  have bounds:=AllocateRetry.scratch_numbers p hn
  have interval:=retry_interval p hn
  have below:(AllocateRetry.scratch p).toNat+16≤(AllocateFlagged.head (AllocateRetry.secondLayout p)).toNat:=by
    rw[interval.1];exact bounds.2.2.1
  have rootNat:(AllocateRetry.scratch p+12).toNat=(AllocateRetry.scratch p).toNat+12:=bounds.2.1
  have initial:readI32 (AllocateRetry.secondLayout p).memory ((AllocateRetry.scratch p).toNat+12)=
      AllocateFlagged.head (AllocateRetry.secondLayout p):=by
    change _=readI32 (AllocateRetry.secondLayout p).memory (AllocateRetry.scratch p+12).toNat
    rw[rootNat]
  apply Eq.trans (b:=readI32 (AllocateRetry.secondLayout p).memory ((AllocateRetry.scratch p).toNat+12)) _ initial
  apply readI32_congr_bytes
  intro i hi
  exact AllocateFlagged.finalMemory_below_head (AllocateRetry.secondLayout p)
    (AllocateRetry.native_second p hn) _ (by omega)

 theorem retry_root(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    readI32 (AllocateRetry.finalMemory p) p.allocator.toNat=
      AllocateFlagged.head (AllocateRetry.secondLayout p):=by
  have spec:=AllocateRetry.searchedMemory_spec p hn
  have bound:p.allocator.toNat+4≤(AllocateRetry.searchedMemory p).byteSize:=by
    rw[spec.2.1];have h:=hn.allocatorBound;omega
  exact (PanicAllocateReadback.read_write_self (AllocateRetry.searchedMemory p) _ _ spec.1 bound).trans
    (retry_saved_head p hn)

 theorem retry_final_word(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p)(address:Nat)
    (above:p.memory.byteSize≤address):
    readI32 (AllocateRetry.finalMemory p) address=readI32 (AllocateRetry.searchedMemory p) address:=by
  have spec:=AllocateRetry.searchedMemory_spec p hn
  have bound:p.allocator.toNat+4≤(AllocateRetry.searchedMemory p).byteSize:=by
    rw[spec.2.1];have h:=hn.allocatorBound;omega
  exact PanicAllocateReadback.read_write_frame (AllocateRetry.searchedMemory p) address p.allocator.toNat _
    spec.1 bound (Or.inr (by have h:=hn.allocatorBound;omega))

 theorem retry_final_head(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    readI32 (AllocateRetry.finalMemory p) (AllocateFlagged.head (AllocateRetry.secondLayout p)).toNat=
      AllocateFlagged.header (AllocateRetry.secondLayout p):=by
  rw[retry_final_word p hn _ (by rw[(retry_interval p hn).1])]
  exact final_head (AllocateRetry.secondLayout p) (AllocateRetry.native_second p hn)

 theorem retry_final_candidate_flag(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    readI32 (AllocateRetry.finalMemory p) ((AllocateFlagged.head (AllocateRetry.secondLayout p)).toNat+8)&&&1=0:=by
  rw[retry_final_word p hn _ (by rw[(retry_interval p hn).1];omega)]
  exact final_candidate_flag (AllocateRetry.secondLayout p) (AllocateRetry.native_second p hn)

 theorem retry_final_split(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p)(size:p.size=29):
    Allocate.SplitNative (AllocateRetry.finalMemory p)
      (readI32 (AllocateRetry.finalMemory p) p.allocator.toNat) 1:=by
  rw[retry_root p hn]
  have native:=retry_next_one_word p hn size
  have he:Allocate.endWord (AllocateRetry.finalMemory p) (AllocateFlagged.head (AllocateRetry.secondLayout p))=
      Allocate.endWord (AllocateRetry.searchedMemory p) (AllocateFlagged.head (AllocateRetry.secondLayout p)):=by
    unfold Allocate.endWord
    rw[retry_final_word p hn _ (by rw[(retry_interval p hn).1])]
  have searched:=AllocateRetry.searchedMemory_spec p hn
  have final:=AllocateRetry.finalMemory_spec p hn
  refine ⟨native.wordsPositive,?_,?_⟩
  · rw[he];exact native.room
  · rw[he,final.2.1,←searched.2.1];exact native.endBound
end WNear.Proofs.AllocationGrowthRemainder
