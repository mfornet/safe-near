import Proofs.AllocateFlaggedCallFrame

/-! Functional-host preservation by the pure Wasm allocator call. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (Layout minimumDone arithmeticDone callbackDone endSubtracted candidateAfter unitsFrom sizeFrom initialAfter maskStore taggedTeeStore)
set_option maxRecDepth 16384
attribute [local irreducible] minimumDone arithmeticDone callbackDone endSubtracted splitAfter
  candidateAfter searched searchAfter callAfter controlAfter Allocate.committed

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    view seed (chargedStore s cost).host=view seed s.host := rfl
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    view seed (paid s op n).host=view seed s.host := by
  induction n with | zero => rfl | succ n ih => exact (view_charge seed (paid s op n) op).trans ih
private theorem view_store32 (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    view seed (storeI32 s index address memory v).host=view seed s.host := rfl
private theorem view_store64 (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt64) :
    view seed (storeI64 s index address memory v).host=view seed s.host := rfl
private theorem view_minimum (seed : NearState) (s : Store NearState) (op : Nat) :
    view seed (minimumDone s op).host=view seed s.host := by
  simp only [minimumDone,arithmeticDone,callbackDone,endSubtracted,Allocate.callbackAfter,
    AllocateUnits.minimumAfter,AllocateUnits.unitsAfter,AllocateUnits.quantumAfter,AllocateUnits.entered9,
    view_paid,view_charge]
private theorem view_candidate (seed : NearState) (s : Store NearState) (op : Nat) :
    view seed (candidateAfter s op).host=view seed s.host := by
  simp only [candidateAfter,unitsFrom,sizeFrom,AllocateUnits.unitsAfter,AllocateUnits.entered9,
    DeallocateListSize.after,DeallocateListSize.entered,view_paid,view_charge]
private theorem view_initialized (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (mutateInitialized s op p).host=view seed s.host := by
  simp only [mutateInitialized,Allocate.initializedStore,Allocate.copiedEndStore,Allocate.clearedStore,
    view_store32,view_store64,view_paid]
private theorem view_control (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (controlAfter s op p).host=view seed s.host := by
  simp only [controlAfter,transferred,flaggedStore,flagStore,clearedStore,clearStore,
    linkedStore,taggedTeeStore,unflaggedStore,maskStore,previousStore,Allocate.taggedStore,
    afterBacklink,view_paid,view_store32]
private theorem view_commit (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    view seed (Allocate.committed s op index memory header).host=view seed s.host := by
  simp only [Allocate.committed,Allocate.markedStore,view_paid,view_store32]
private theorem view_split (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (splitAfter s op p).host=view seed s.host := by
  simp only [splitAfter,mutateAfter,view_commit,view_control,view_initialized,view_minimum]

theorem callAfter_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h : view s.host (callAfter s op p).host=view s.host s.host := by
    simp only [callAfter,searchAfter,searched,view_paid,view_split,view_candidate,initialAfter,
      entered,view_charge]
  exact h

end WNear.Proofs.AllocateFlagged
