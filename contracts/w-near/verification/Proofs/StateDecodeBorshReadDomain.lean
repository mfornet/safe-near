import Proofs.StateDecodeBorshReadAllocation

/-! Original template compatibility completes the actual prepared decoder's
accepted domain. All four compatibility equations concern original fields. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

structure AcceptedDomain(p:Layout)(q:StateDecodeVectorCopy.Layout):Prop extends AllocationDomain p q where
  module:q.mi=p.mi
  memoryIndex:q.memoryIndex=p.memoryIndex
  globalIndex:q.globalIndex=p.globalIndex
  global:q.globalVector={p.global with value:=.i32 (StateDecodePrefix.scratch p.toPrefix)}

theorem wrapper_count(p:Layout)(hn:Native p):
    StateDecodeBorshWrapper.count (actualWrapper p)=count p:=actual_count p hn

theorem allocation_domain(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    StateDecodePrefix.AllocationDomain (actualWrapper p).toPrefix (actualAllocation p q):=by
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have nc:StateDecodePrefix.count (actualWrapper p).toPrefix=count p:=actual_count p hn
  have allocator:=hd.allocatorAbove
  have head:=hd.headAbove
  refine ⟨allocation_native p q hn hd,rfl,?_,hd.sp,hd.out,hd.source,?_,?_,?_,?_⟩
  · change q.size=StateDecodePrefix.count (actualWrapper p).toPrefix
    rw[nc];exact hd.size
  · change p.sp.toNat≤q.allocator.toNat;omega
  · change p.sp.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p q).toPositive)).toNat
    rw[head_eq p q hn hd];omega
  · change p.slice.toNat+8≤(AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p q).toPositive)).toNat
    rw[head_eq p q hn hd];omega
  · change q.allocator.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤q.allocator.toNat
    right;omega

theorem accepted_domain(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    StateDecodeBorsh.AcceptedDomain (actualWrapper p).toBorsh (actualAllocation p q):=by
  have geo:=stack_geometry p hn
  have original:=allocation_domain p q hn hd.toAllocationDomain
  have inner:StateDecodePrefix.AcceptedDomain (actualWrapper p).toPrefix (actualAllocation p q):=
    ⟨original,hd.module,hd.memoryIndex,hd.globalIndex,hd.global⟩
  refine ⟨inner,?_⟩
  change p.out.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat
  left;omega

theorem callback_bound(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    (actualWrapper p).sp.toNat≤1057464+16 ∧
    (1057464+20≤(actualWrapper p).slice.toNat ∨(actualWrapper p).slice.toNat+8≤1057464+16):=by
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have callback:=hd.callbackAbove
  change p.sp.toNat≤1057464+16 ∧(1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
  exact ⟨by omega,Or.inr (by omega)⟩
end WNear.Proofs.StateDecodeBorshRead
