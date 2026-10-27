import Proofs.AllocateEmptyCall
import Proofs.AllocateSearchGasCost

/-! Exact resource frame for the empty-list580 call. -/
namespace WNear.Proofs.AllocateEmpty
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_charge gasUnits_paid)

theorem callAfter_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (37*op+rest)) :
    (callAfter s op).host.gas.burnt=s.host.gas.burnt+37*op ∧
    (callAfter s op).host.gas.promises=s.host.gas.promises ∧
    (callAfter s op).host.gas.Credits rest := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have entered := first.trans (gasUnits_charge (chargedStore s op) op 15)
  have all := entered.trans (gasUnits_paid (AllocateSearch.entered s op) op 21)
  exact all rest hc

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    view seed (paid s op n).host=view seed s.host := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem paid_frame (s : Store NearState) (op count : Nat) :
    (paid s op count).mems=s.mems ∧ (paid s op count).modules=s.modules ∧
    (paid s op count).funcs=s.funcs ∧ (paid s op count).globals=s.globals ∧
    (paid s op count).tables=s.tables := by
  induction count with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih => exact ih

theorem callAfter_frame (s : Store NearState) (op : Nat) :
    (callAfter s op).mems=s.mems ∧ (callAfter s op).modules=s.modules ∧
    (callAfter s op).funcs=s.funcs ∧ (callAfter s op).globals=s.globals ∧
    (callAfter s op).tables=s.tables ∧
    {(callAfter s op).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h := paid_frame (AllocateSearch.entered s op) op 21
  have hv := view_paid s.host (AllocateSearch.entered s op) op 21
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,?_⟩
  exact hv
end WNear.Proofs.AllocateEmpty
