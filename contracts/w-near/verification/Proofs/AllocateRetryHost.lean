import Proofs.AllocateRetryState
import Proofs.AllocatePositiveGas

/-! Functional-host preservation by the real growth-and-retry allocation path. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_reset (seed old host : NearState) :
    view seed {host with gas:=old.gas,gasProfile:=old.gasProfile}=view seed host := rfl
private theorem view_rebase (seed base host : NearState) (h : view base host=base) :
    view seed host=view seed base := by
  have result := congrArg (view seed) h
  change view seed {host with gas:=base.gas,gasProfile:=base.gasProfile}=view seed base at result
  simpa only [view_reset] using result
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    view seed (chargedStore s cost).host=view seed s.host := rfl
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    view seed (paid s op n).host=view seed s.host := by
  induction n with
  | zero => rfl
  | succ n ih => exact (view_charge seed (paid s op n) op).trans ih
private theorem view_global (seed : NearState) (s : Store NearState) (index : Nat) (v : Value) :
    view seed (setGlobal s index v).host=view seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    view seed (storeI32 s index address memory v).host=view seed s.host := rfl

attribute [local irreducible] reserved prefixed firstAttempt firstMiss beforeGrow grown checked oldLinked relinked retried found updated after
  AllocateGrowth.callAfter AllocateGrowth.delta memoryGrowCost growthLayout AllocateFlagged.callAfter AllocateEmpty.callAfter

private theorem view_round (seed : NearState) (s : Store NearState) (op : Nat) :
    view seed (Allocate.roundedStore s op).host=view seed s.host := by
  have source : view (paid s op 1).host (DeallocateAlign.after570 (paid s op 1) op).host=(paid s op 1).host :=
    DeallocateAlign.after570_functional_host (paid s op 1) op
  have h := view_rebase seed (paid s op 1).host (DeallocateAlign.after570 (paid s op 1) op).host source
  unfold Allocate.roundedStore
  rw [view_paid,h,view_paid]
private theorem view_prefix (seed : NearState) (s : Store NearState) (op index : Nat) (stack allocator : UInt32) (memory : Memory) :
    view seed (Allocate.prefixAfter s op index stack allocator memory).host=view seed s.host := by
  unfold Allocate.prefixAfter Allocate.savedHead
  rw [view_store,view_paid,view_round]
private theorem view_positive_prefix (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocatePositive.Layout) :
    view seed (AllocatePositive.prefixed s op p).host=view seed s.host := by
  unfold AllocatePositive.prefixed AllocatePositive.reserved
  rw [view_prefix,view_paid,view_global,view_paid]
private theorem view_empty (seed : NearState) (s : Store NearState) (op : Nat) :
    view seed (AllocateEmpty.callAfter s op).host=view seed s.host := by
  have h : view s.host (AllocateEmpty.callAfter s op).host=s.host := (AllocateEmpty.callAfter_frame s op).2.2.2.2.2
  exact view_rebase seed s.host (AllocateEmpty.callAfter s op).host h
private theorem view_growth (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocateGrowth.Layout) :
    view seed (AllocateGrowth.callAfter cfg s p).host=view seed s.host := by
  have h : view s.host (AllocateGrowth.callAfter cfg s p).host=s.host := AllocateGrowth.callAfter_functional_host cfg s p
  exact view_rebase seed s.host (AllocateGrowth.callAfter cfg s p).host h
private theorem view_flagged (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocateSearch.Layout) :
    view seed (AllocateFlagged.callAfter s op p).host=view seed s.host := by
  have h : view s.host (AllocateFlagged.callAfter s op p).host=s.host := AllocateFlagged.callAfter_functional_host s op p
  exact view_rebase seed s.host (AllocateFlagged.callAfter s op p).host h

private theorem view_prefixed (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (prefixed s op p).host=view seed s.host := by
  unfold prefixed
  exact view_positive_prefix seed s op p.toLayout
private theorem view_first (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (firstAttempt s op p).host=view seed s.host := by
  unfold firstAttempt
  rw [view_empty,view_paid,view_prefixed]
private theorem view_beforeGrow (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (beforeGrow s op p).host=view seed s.host := by
  unfold beforeGrow firstMiss
  rw [view_paid,view_paid,view_first]
private theorem view_grown (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (grown cfg s p).host=view seed s.host := by
  unfold grown
  rw [view_growth,view_beforeGrow]
private theorem view_checked (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (checked cfg s p).host=view seed s.host := by
  unfold checked
  rw [view_paid,view_grown]
private theorem view_oldLinked (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (oldLinked cfg s p).host=view seed s.host := by
  unfold oldLinked
  rw [view_store,view_paid,view_checked]
private theorem view_relinked (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (relinked cfg s p).host=view seed s.host := by
  unfold relinked
  rw [view_store,view_paid,view_oldLinked]
private theorem view_retried (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (retried cfg s p).host=view seed s.host := by
  unfold retried
  rw [view_flagged,view_paid,view_relinked]
private theorem view_found (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (found cfg s p).host=view seed s.host := by
  unfold found
  rw [view_paid,view_retried]
private theorem view_updated (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (updated cfg s p).host=view seed s.host := by
  unfold updated
  rw [view_store,view_paid,view_found]

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p).host=s.host
  unfold after
  rw [view_paid,view_global,view_paid,view_updated]
  rfl
end WNear.Proofs.AllocateRetry
