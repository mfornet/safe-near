import Proofs.AllocatePositiveSkipFrame
import Proofs.AllocateSearchGasCost

/-! Exact ordinary-gas accounting and functional-host frames of positive f581. -/
namespace WNear.Proofs.AllocatePositiveSkip
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
set_option maxRecDepth 16384
attribute [local irreducible] reserved prefixed searched found updated after
  Allocate.prefixAfter Allocate.roundedStore AllocateSkip.callAfter

private theorem units_skip_call (s : Store NearState) (op : Nat) (p : AllocateSearch.Layout) :
    GasUnits s (AllocateSkip.callAfter s op p) op 345 := by
  intro rest hc
  exact AllocateSkip.callAfter_gas s op rest p hc

private theorem units_round (s : Store NearState) (op : Nat) : GasUnits s (Allocate.roundedStore s op) op 43 := by
  have mid : GasUnits (paid s op 1) (DeallocateAlign.after570 (paid s op 1) op) op 41 := by
    intro rest hc
    have h := DeallocateAlign.after570_gas (paid s op 1) op rest hc
    exact ⟨h.1,h.2,DeallocateAlign.after570_credits (paid s op 1) op rest hc⟩
  have a := (gasUnits_paid s op 1).trans mid
  have b := a.trans (gasUnits_paid (DeallocateAlign.after570 (paid s op 1) op) op 1)
  simpa only [Allocate.roundedStore,Nat.reduceAdd] using b
private theorem units_prefix (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory) :
    GasUnits s (Allocate.prefixAfter s op index scratch allocator memory) op 47 := by
  have tail : GasUnits (Allocate.roundedStore s op) (Allocate.savedHead (Allocate.roundedStore s op) op index scratch allocator memory) op 4 :=
    (gasUnits_paid (Allocate.roundedStore s op) op 4).host_eq rfl
  have h := (units_round s op).trans tail
  simpa only [Allocate.prefixAfter,Nat.reduceAdd] using h
 theorem gasUnits_reserved (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (reserved s op p) op 5 := by
  unfold reserved
  exact (gasUnits_paid s op 5).host_eq rfl
 theorem gasUnits_prefixed (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (prefixed s op p) op 54 := by
  have a := (gasUnits_reserved s op p).trans (gasUnits_paid (reserved s op p) op 2)
  have b := a.trans (units_prefix (paid (reserved s op p) op 2) op p.memoryIndex (scratch p) p.allocator p.memory)
  simpa only [prefixed,Nat.reduceAdd] using b
 theorem gasUnits_searched (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (searched s op p) op 406 := by
  have a := (gasUnits_prefixed s op p).trans (gasUnits_paid (prefixed s op p) op 7)
  have b := a.trans (units_skip_call (paid (prefixed s op p) op 7) op (searchLayout p))
  simpa only [searched,Nat.reduceAdd] using b
 theorem gasUnits_found (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (found s op p) op 408 := by
  have a := (gasUnits_searched s op p).trans (gasUnits_paid (searched s op p) op 2)
  simpa only [found,Nat.reduceAdd] using a
 theorem gasUnits_updated (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (updated s op p) op 412 := by
  have tail : GasUnits (found s op p) (updated s op p) op 4 :=
    (gasUnits_paid (found s op p) op 4).host_eq (by rw [updated,storeI32_host])
  exact (gasUnits_found s op p).trans tail
 theorem gasUnits_after (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (after s op p) op 417 := by
  have tail : GasUnits (updated s op p) (setGlobal (paid (updated s op p) op 4) p.globalIndex (.i32 p.sp)) op 4 :=
    (gasUnits_paid (updated s op p) op 4).host_eq rfl
  have a := (gasUnits_updated s op p).trans tail
  have b := a.trans (gasUnits_paid (setGlobal (paid (updated s op p) op 4) p.globalIndex (.i32 p.sp)) op 1)
  simpa only [after,Nat.reduceAdd] using b

 theorem reserved_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (5*op+rest)) :
    (reserved s op p).host.gas.Credits rest := (gasUnits_reserved s op p rest hc).2.2
 theorem prefixed_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (54*op+rest)) :
    (prefixed s op p).host.gas.Credits rest := (gasUnits_prefixed s op p rest hc).2.2
 theorem searched_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (406*op+rest)) :
    (searched s op p).host.gas.Credits rest := (gasUnits_searched s op p rest hc).2.2
 theorem found_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (408*op+rest)) :
    (found s op p).host.gas.Credits rest := (gasUnits_found s op p rest hc).2.2
 theorem updated_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (412*op+rest)) :
    (updated s op p).host.gas.Credits rest := (gasUnits_updated s op p rest hc).2.2
 theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (417*op+rest)) :
    (after s op p).host.gas.Credits rest := (gasUnits_after s op p rest hc).2.2
 theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (417*op+rest)) :
    (after s op p).host.gas.burnt=s.host.gas.burnt+417*op ∧
    (after s op p).host.gas.promises=s.host.gas.promises ∧ (after s op p).host.gas.Credits rest :=
  gasUnits_after s op p rest hc

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    view seed (chargedStore s cost).host=view seed s.host := rfl
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero => rfl | succ n ih => exact (view_charge seed (paid s op n) op).trans ih
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host := rfl
private theorem view_round (seed : NearState) (s : Store NearState) (op : Nat) : view seed (Allocate.roundedStore s op).host=view seed s.host := by
  have h := congrArg (view seed) (DeallocateAlign.after570_functional_host (paid s op 1) op)
  simp only [view] at h
  simp only [Allocate.roundedStore,view_paid]
  exact h.trans (view_paid seed s op 1)
private theorem view_prefix (seed : NearState) (s : Store NearState) (op index : Nat) (scratch allocator : UInt32) (memory : Memory) :
    view seed (Allocate.prefixAfter s op index scratch allocator memory).host=view seed s.host := by
  simp only [Allocate.prefixAfter,Allocate.savedHead,view_store,view_paid,view_round]
private theorem view_search (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocateSearch.Layout) :
    view seed (AllocateSkip.callAfter s op p).host=view seed s.host := by
  have h := congrArg (view seed) (AllocateSkip.callAfter_functional_host s op p)
  simpa only [view] using h
private theorem view_reserved (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (reserved s op p).host=view seed s.host := by
  rw [reserved,view_global,view_paid]
private theorem view_prefixed (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (prefixed s op p).host=view seed s.host := by
  rw [prefixed,view_prefix,view_paid,view_reserved]
private theorem view_searched (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (searched s op p).host=view seed s.host := by
  rw [searched,view_search,view_paid,view_prefixed]
private theorem view_found (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (found s op p).host=view seed s.host := by
  rw [found,view_paid,view_searched]
private theorem view_updated (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (updated s op p).host=view seed s.host := by
  rw [updated,view_store,view_paid,view_found]
 theorem after_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after s op p).host=s.host
  rw [after,view_paid,view_global,view_paid,view_updated]
  rfl

end WNear.Proofs.AllocatePositiveSkip
