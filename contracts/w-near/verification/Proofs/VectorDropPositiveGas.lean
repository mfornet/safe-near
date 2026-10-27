import Proofs.VectorDropPositiveState

/-! Exact gas consumed before the concrete heap deallocator is called. -/
namespace WNear.Proofs.VectorDropPositive
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
open WNear.Proofs.VectorDrop
set_option maxRecDepth 16384

private theorem charge_gas (s : Store NearState) (cost rest : Nat)
    (hc : s.host.gas.Credits (cost + rest)) :
    (chargedStore s cost).host.gas.burnt = s.host.gas.burnt + cost ∧
    (chargedStore s cost).host.gas.promises = s.host.gas.promises := by
  have h := GasCounter.burn_credits s.host.gas cost rest hc
  exact ⟨h.2.1, h.2.2.1⟩

private theorem staged_gas (s : Store NearState) (op first activation last rest : Nat)
    (hc : s.host.gas.Credits ((first + 1 + activation + last) * op + rest)) :
    (paid (chargedStore (chargedStore (paid s op first) op) (activation * op)) op last).host.gas.burnt =
      s.host.gas.burnt + (first + 1 + activation + last) * op ∧
    (paid (chargedStore (chargedStore (paid s op first) op) (activation * op)) op last).host.gas.promises = s.host.gas.promises := by
  have hfirst := paid_gas s op first ((1 + activation + last) * op + rest) (hc.mono (by simp only [Nat.add_mul, Nat.one_mul]; omega))
  have cfirst := paid_credits s op first ((1 + activation + last) * op + rest) (hc.mono (by simp only [Nat.add_mul, Nat.one_mul]; omega))
  have hcall := charge_gas (paid s op first) op ((activation + last) * op + rest) (cfirst.mono (by simp only [Nat.add_mul, Nat.one_mul]; omega))
  have ccall := StorePair.charged_credits (paid s op first) op ((activation + last) * op + rest) (cfirst.mono (by simp only [Nat.add_mul, Nat.one_mul]; omega))
  have hentry := charge_gas (chargedStore (paid s op first) op) (activation * op) (last * op + rest) (ccall.mono (by simp only [Nat.add_mul]; omega))
  have centry := StorePair.charged_credits (chargedStore (paid s op first) op) (activation * op) (last * op + rest) (ccall.mono (by simp only [Nat.add_mul]; omega))
  have hlast := paid_gas (chargedStore (chargedStore (paid s op first) op) (activation * op)) op last rest centry
  refine ⟨?_, hlast.2.trans (hentry.2.trans (hcall.2.trans hfirst.2))⟩
  rw [hlast.1, hentry.1, hcall.1, hfirst.1]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem before747_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (12 * op + rest)) :
    (before747 s op).host.gas.burnt = s.host.gas.burnt + 12 * op ∧
    (before747 s op).host.gas.promises = s.host.gas.promises := by
  exact staged_gas s op 1 9 1 rest hc

theorem before777_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (31 * op + rest)) :
    (before777 s op).host.gas.burnt = s.host.gas.burnt + 31 * op ∧
    (before777 s op).host.gas.promises = s.host.gas.promises := by
  have hp := before747_gas s op (19 * op + rest) (hc.mono (by omega))
  have cp := before747_credits s op (19 * op + rest) (hc.mono (by omega))
  have h := staged_gas (before747 s op) op 0 9 9 rest cp
  refine ⟨?_, h.2.trans hp.2⟩
  change (paid (entered (before747 s op) op) op 9).host.gas.burnt = _
  have hb : (before777 s op).host.gas.burnt = (before747 s op).host.gas.burnt + 19 * op := h.1
  change (before777 s op).host.gas.burnt = _
  rw [hb, hp.1]; omega

theorem before311_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (48 * op + rest)) :
    (before311 s op).host.gas.burnt = s.host.gas.burnt + 48 * op ∧
    (before311 s op).host.gas.promises = s.host.gas.promises := by
  have hp := before777_gas s op (17 * op + rest) (hc.mono (by omega))
  have cp := before777_credits s op (17 * op + rest) (hc.mono (by omega))
  have h := staged_gas (before777 s op) op 0 10 6 rest cp
  refine ⟨?_, h.2.trans hp.2⟩
  change (paid (tripleEntry (before777 s op) op) op 6).host.gas.burnt = _
  have hb : (before311 s op).host.gas.burnt = (before777 s op).host.gas.burnt + 17 * op := h.1
  change (before311 s op).host.gas.burnt = _
  rw [hb, hp.1]; omega

theorem before237_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (62 * op + rest)) :
    (before237 s op).host.gas.burnt = s.host.gas.burnt + 62 * op ∧
    (before237 s op).host.gas.promises = s.host.gas.promises := by
  have hp := before311_gas s op (14 * op + rest) (hc.mono (by omega))
  have cp := before311_credits s op (14 * op + rest) (hc.mono (by omega))
  have h := staged_gas (before311 s op) op 0 10 3 rest cp
  refine ⟨?_, h.2.trans hp.2⟩
  change (paid (tripleEntry (before311 s op) op) op 3).host.gas.burnt = _
  have hb : (before237 s op).host.gas.burnt = (before311 s op).host.gas.burnt + 14 * op := h.1
  change (before237 s op).host.gas.burnt = _
  rw [hb, hp.1]; omega
end WNear.Proofs.VectorDropPositive
