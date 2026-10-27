import Proofs.DeallocateListSize

/-! Structural and exact gas frame for the actual f576 normal call. -/
namespace WNear.Proofs.DeallocateListSize
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_gas)

theorem after_resources (s : Store NearState) (op : Nat) :
    {after s op with host := s.host} = s := by
  simp only [after, entered, paid, chargedStore]

theorem after_host (s : Store NearState) (op : Nat) :
    {(after s op).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [after, entered, paid, chargedStore, chargeHost]

theorem after_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (25 * op + rest)) :
    (after s op).host.gas.burnt = s.host.gas.burnt + 25 * op ∧
    (after s op).host.gas.promises = s.host.gas.promises ∧
    (after s op).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (24 * op + rest) (hc.mono (by omega))
  have act := GasCounter.burn_credits (chargedStore s op).host.gas (9 * op) (15 * op + rest) (hop.2.2.2.mono (by omega))
  have body := paid_gas (entered s op) op 15 rest act.2.2.2
  refine ⟨?_, body.2.trans (act.2.2.1.trans hop.2.2.1), after_credits s op rest hc⟩
  change (paid (entered s op) op 15).host.gas.burnt = _
  rw [body.1]
  change ((chargedStore s op).host.gas.burn (9 * op)).1.burnt + 15 * op = _
  rw [act.2.1]
  change (s.host.gas.burn op).1.burnt + 9 * op + 15 * op = _
  rw [hop.2.1]; omega

end WNear.Proofs.DeallocateListSize
