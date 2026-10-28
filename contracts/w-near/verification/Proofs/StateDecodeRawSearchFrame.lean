import Proofs.StateDecodeRawOldFrame

/-! Real allocator-result wrappers preserve search post-memory outside their
actual root and result-record writes. No old-heap comparison is substituted. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

 theorem finalMemory_search_frame(p:Layout)(hn:Native p)(j:Nat)
    (outside:j<p.allocator.toNat ∨p.allocator.toNat+4≤j):
    (finalMemory p).read8 j=(searchedMemory p).read8 j:=by
  have n:=scratch_numbers p hn
  have saved:=writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hn.wf
    (by have b:=n.2.2.1;omega)
  have search:=AllocateSearch.final_shape (searchLayout p) hn.search
  have size:(searchedMemory p).byteSize=p.memory.byteSize:=search.size.trans saved.2.1
  have bound:p.allocator.toNat+4≤(searchedMemory p).byteSize:=by rw[size];exact hn.allocatorBound
  have final:=writeI32_spec (searchedMemory p) p.allocator.toNat
    (readI32 (searchedMemory p) ((scratch p).toNat+12)) search.wf bound
  unfold finalMemory
  rw[final.2.2.2 j]
  exact ite_eq_right (by rcases outside with h|h <;> omega)
end WNear.Proofs.AllocatePositive

namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 laidOutMemory AllocatePositive.finalMemory

private theorem two_bytes(memory:Memory)(a b:Nat)(x y:UInt32)(j:Nat)(hw:memory.wf)
    (ha:a+4≤memory.byteSize)(hb:b+4≤memory.byteSize)(hja:a+4≤j)(hjb:b+4≤j):
    (writeI32 (writeI32 memory a x) b y).read8 j=memory.read8 j:=by
  have first:=writeI32_spec memory a x hw ha
  have second:=writeI32_spec (writeI32 memory a x) b y first.1 (by rw[first.2.1];exact hb)
  rw[second.2.2.2 j,ite_eq_right (show ¬(b≤j ∧j<b+4) by omega),first.2.2.2 j,
    ite_eq_right (show ¬(a≤j ∧j<a+4) by omega)]

 theorem allocated_search_frame(p:Layout)(hn:Native p)(j:Nat)
    (outside:j<p.allocator.toNat ∨p.allocator.toNat+4≤j):
    (allocatedMemory p).read8 j=(AllocatePositive.searchedMemory (actualPositive p)).read8 j:=by
  unfold allocatedMemory
  exact AllocatePositive.finalMemory_search_frame (actualPositive p) (allocation_native p hn) j outside

 theorem memory769_search_frame(p:Layout)(hn:Native p)(j:Nat)(above:p.spRaw.toNat≤j)
    (outside:j<p.allocator.toNat ∨p.allocator.toNat+4≤j):
    (memory769 p).read8 j=(AllocatePositive.searchedMemory (actualPositive p)).read8 j:=by
  have a:=allocated_spec p hn
  have b:=memory770_spec p hn
  have n:=record_numbers p hn
  have lo:=hn.spLower
  have hi:=hn.spBound
  have first:(memory770 p).read8 j=(allocatedMemory p).read8 j:=by
    unfold memory770 highMemory770
    apply two_bytes _ _ _ _ _ j a.1
    all_goals first | (rw[a.2.1,n.1];omega) | (rw[n.1];omega)
  have second:(memory769 p).read8 j=(memory770 p).read8 j:=by
    unfold memory769 lowMemory769
    apply two_bytes _ _ _ _ _ j b.1
    all_goals first | (rw[b.2.1,n.2.1];omega) | (rw[n.2.1];omega)
  exact second.trans (first.trans (allocated_search_frame p hn j outside))

 theorem finalMemory_search_frame(p:Layout)(hn:Native p)(j:Nat)(above:p.spRaw.toNat≤j)
    (root:j<p.allocator.toNat ∨p.allocator.toNat+4≤j)
    (output:j<p.outRaw.toNat ∨p.outRaw.toNat+8≤j):
    (finalMemory p).read8 j=(AllocatePositive.searchedMemory (actualPositive p)).read8 j:=
  ((finalMemory_spec p hn).2.2.2.2.2 j output).trans (memory769_search_frame p hn j above root)
end WNear.Proofs.StateDecodeRaw
