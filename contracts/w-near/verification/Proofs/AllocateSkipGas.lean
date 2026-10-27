import Proofs.AllocateSkipResult
import Proofs.AllocateSearchGasCost

/-! Exact billing and functional-host frames of the selected one-hop580 call. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] after callAfter resumed hopped advanced candidateAfter AllocateSearch.searched
  AllocateSearch.minimumDone AllocateSearch.arithmeticDone AllocateSearch.callbackDone AllocateSearch.endSubtracted
  AllocateSearch.initialized AllocateSearch.linked AllocateSearch.splitAfter AllocateSearch.controlAfter Allocate.committed Allocate.callbackAfter

private theorem units_entered9 (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.entered9 s op) op 10 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have h := first.trans (gasUnits_charge (chargedStore s op) op 9)
  simpa only [AllocateUnits.entered9,Nat.one_mul,Nat.reduceAdd] using h

private theorem units_units (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.unitsAfter s op) op 19 := by
  exact (units_entered9 s op).trans (gasUnits_paid (AllocateUnits.entered9 s op) op 9)

private theorem units_size (s : Store NearState) (op : Nat) : GasUnits s (DeallocateListSize.after s op) op 25 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have a := first.trans (gasUnits_charge (chargedStore s op) op 9)
  have b := a.trans (gasUnits_paid (DeallocateListSize.entered s op) op 15)
  simpa only [DeallocateListSize.after,DeallocateListSize.entered,Nat.reduceAdd] using b

private theorem units_candidate (s : Store NearState) (op : Nat) : GasUnits s (candidateAfter s op) op 60 := by
  have a := (gasUnits_paid s op 10).trans (gasUnits_paid (paid s op 10) op 1)
  have b := a.trans (units_units (paid (paid s op 10) op 1) op)
  have c := b.trans (gasUnits_paid (AllocateUnits.unitsAfter (paid (paid s op 10) op 1) op) op 1)
  have d := c.trans (gasUnits_paid (unitsFrom (paid s op 10) op) op 1)
  have e := d.trans (units_size (paid (unitsFrom (paid s op 10) op) op 1) op)
  have f := e.trans (gasUnits_paid (DeallocateListSize.after (paid (unitsFrom (paid s op 10) op) op 1) op) op 3)
  simpa only [candidateAfter,sizeFrom,unitsFrom,Nat.reduceAdd] using f

 theorem gasUnits_hopped (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (hopped s op p) op 67 := by
  have write : GasUnits (candidateAfter s op) (advanced s op p) op 5 := by
    apply (gasUnits_paid (candidateAfter s op) op 5).host_eq
    rw [advanced,storeI32_host]
  have a := (units_candidate s op).trans write
  have b := a.trans (gasUnits_charge (advanced s op p) op 2)
  simpa only [hopped,Nat.reduceAdd] using b
 theorem gasUnits_resumed (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (resumed s op p) op 71 := by
  have a := (gasUnits_hopped s op p).trans (gasUnits_paid (hopped s op p) op 4)
  simpa only [resumed,Nat.reduceAdd] using a
private theorem units_searched (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (AllocateSearch.searched s op p) op 236 := by
  have a := (units_candidate s op).trans (AllocateSearch.gasUnits_splitAfter (candidateAfter s op) op p)
  simpa only [AllocateSearch.searched,Nat.reduceAdd] using a
 theorem gasUnits_after (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (after s op p) op 329 := by
  have a := (gasUnits_paid s op 16).trans (gasUnits_paid (initialAfter s op) op 5)
  have aa : GasUnits s (before s op) op 21 := by simpa only [before,initialAfter,Nat.reduceAdd] using a
  have b := aa.trans (gasUnits_resumed (before s op) op p)
  have c := b.trans (units_searched (resumed (before s op) op p) op (nextLayout p))
  have d := c.trans (gasUnits_paid (AllocateSearch.searched (resumed (before s op) op p) op (nextLayout p)) op 1)
  simpa only [after,Nat.reduceAdd] using d
 theorem gasUnits_entered (s : Store NearState) (op : Nat) : GasUnits s (entered s op) op 16 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have a := first.trans (gasUnits_charge (chargedStore s op) op 15)
  simpa only [entered,Nat.reduceAdd] using a
 theorem callAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (345*op+rest)) :
    (callAfter s op p).host.gas.burnt=s.host.gas.burnt+345*op ∧
    (callAfter s op p).host.gas.promises=s.host.gas.promises ∧ (callAfter s op p).host.gas.Credits rest := by
  have a := (gasUnits_entered s op).trans (gasUnits_after (entered s op) op p)
  have all : GasUnits s (callAfter s op p) op 345 := by simpa only [callAfter,Nat.reduceAdd] using a
  exact all rest hc

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
    view seed (initialized s op p).host=view seed s.host := by
  simp only [initialized,Allocate.initializedStore,Allocate.copiedEndStore,Allocate.clearedStore,
    view_store32,view_store64,view_paid,view_minimum]
private theorem view_control (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (controlAfter s op p).host=view seed s.host := by
  have h := congrArg (view seed) (controlAfter_host s op p)
  simp only [view] at h ⊢
  exact h
private theorem view_commit (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    view seed (Allocate.committed s op index memory header).host=view seed s.host := by
  simp only [Allocate.committed,Allocate.markedStore,view_paid,view_store32]
private theorem view_split (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (splitAfter s op p).host=view seed s.host := by
  simp only [splitAfter,view_commit,linked,view_control,view_initialized]


private theorem view_resumed (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (resumed s op p).host=view seed s.host := by
  rw [resumed,view_paid,hopped,view_charge,advanced,view_store32,view_paid,view_candidate]
private theorem view_searched (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (AllocateSearch.searched s op p).host=view seed s.host := by
  rw [AllocateSearch.searched,view_split,view_candidate]
 theorem after_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after s op p).host=s.host
  rw [after,view_paid,view_searched,view_resumed,before,view_paid,initialAfter,view_paid]
  rfl
 theorem callAfter_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h := congrArg (view s.host) (after_functional_host (entered s op) op p)
  simpa only [view,callAfter,entered,chargedStore,chargeHost] using h
end
end WNear.Proofs.AllocateSkip
