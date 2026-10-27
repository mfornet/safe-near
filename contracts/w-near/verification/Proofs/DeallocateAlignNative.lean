import Proofs.DeallocateAlignCall

/-! Native integer sufficient conditions and functional/gas frames for the
actual deployed checked ceiling-division calls. -/
namespace WNear.Proofs.DeallocateAlign
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_gas paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

/-- Original unsigned bounds imply both actual guard comparisons are false. -/
theorem checks (a b : UInt32) (hb : 0 < b.toNat) (hs : a.toNat + b.toNat < 2 ^ 32) :
    Numeric.irelop32 .lt_u (a + b) a = false ∧
    Numeric.irelop32 .gt_u (a + b + 4294967295) (a + b) = false ∧ b ≠ 0 := by
  have sumNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt hs]
  have adjustedNat : (a + b + 4294967295).toNat = a.toNat + b.toNat - 1 := by
    rw [UInt32.toNat_add, sumNat]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have addCheck : ¬ (a + b < a) := by
    rw [UInt32.lt_iff_toNat_lt, sumNat]
    omega
  have subCheck : ¬ (a + b < a + b + 4294967295) := by
    rw [UInt32.lt_iff_toNat_lt, sumNat, adjustedNat]
    omega
  have nonzero : b ≠ 0 := by intro he; subst b; simp at hb
  exact ⟨by simpa [Numeric.irelop32] using addCheck,
    by simpa [Numeric.irelop32] using subCheck, nonzero⟩

/-- The returned Wasm word is exactly the natural ceiling-division formula. -/
theorem quotient_toNat (a b : UInt32) (hb : 0 < b.toNat) (hs : a.toNat + b.toNat < 2 ^ 32) :
    (quotient a b).toNat = (a.toNat + b.toNat - 1) / b.toNat := by
  have sumNat : (a + b).toNat = a.toNat + b.toNat := by rw [UInt32.toNat_add, Nat.mod_eq_of_lt hs]
  have adjustedNat : (a + b + 4294967295).toNat = a.toNat + b.toNat - 1 := by
    rw [UInt32.toNat_add, sumNat]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  rw [quotient, UInt32.toNat_div, adjustedNat]

theorem checks570 (a : UInt32) (ha : a.toNat + 4 < 2 ^ 32) :
    Numeric.irelop32 .lt_u (a + 4) a = false ∧
    Numeric.irelop32 .gt_u (a + 4 + 4294967295) (a + 4) = false := by
  have h := checks a 4 (by decide) (by simpa using ha)
  exact ⟨h.1, h.2.1⟩

theorem quotient570_toNat (a : UInt32) (ha : a.toNat + 4 < 2 ^ 32) :
    (quotient a 4).toNat = (a.toNat + 3) / 4 := by
  have h := quotient_toNat a 4 (by decide) (by simpa using ha)
  simpa using h


/-- All memory, globals, tables, function and module instances are retained. -/
theorem after568_resources (s : Store NearState) (op : Nat) :
    {after568 s op with host := s.host} = s := by
  simp only [after568, entered568, paid, chargedStore]

theorem after570_resources (s : Store NearState) (op : Nat) :
    {after570 s op with host := s.host} = s := by
  simp only [after570, bodyAfter570, after568, entered568, entered570, paid, chargedStore]

private theorem charge_gas (s : Store NearState) (cost rest : Nat)
    (hc : s.host.gas.Credits (cost + rest)) :
    (chargedStore s cost).host.gas.burnt = s.host.gas.burnt + cost ∧
    (chargedStore s cost).host.gas.promises = s.host.gas.promises := by
  have h := GasCounter.burn_credits s.host.gas cost rest hc
  exact ⟨h.2.1, h.2.2.1⟩

theorem after568_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (29 * op + rest)) :
    (after568 s op).host.gas.burnt = s.host.gas.burnt + 29 * op ∧
    (after568 s op).host.gas.promises = s.host.gas.promises := by
  have h1 := charge_gas s op (28 * op + rest) (hc.mono (by omega))
  have c1 := StorePair.charged_credits s op (28 * op + rest) (hc.mono (by omega))
  have h10 := charge_gas (chargedStore s op) (10 * op) (18 * op + rest) (c1.mono (by omega))
  have ca := entered568_credits s op (18 * op + rest) (hc.mono (by omega))
  have body := paid_gas (entered568 s op) op 18 rest ca
  have entry : (entered568 s op).host.gas.burnt = s.host.gas.burnt + 11 * op := by
    change (chargedStore (chargedStore s op) (10 * op)).host.gas.burnt = _
    rw [h10.1, h1.1]; omega
  refine ⟨?_, body.2.trans (h10.2.trans h1.2)⟩
  change (paid (entered568 s op) op 18).host.gas.burnt = _
  rw [body.1, entry]; omega

theorem after570_gas (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (41 * op + rest)) :
    (after570 s op).host.gas.burnt = s.host.gas.burnt + 41 * op ∧
    (after570 s op).host.gas.promises = s.host.gas.promises := by
  have h1 := charge_gas s op (40 * op + rest) (hc.mono (by omega))
  have c1 := StorePair.charged_credits s op (40 * op + rest) (hc.mono (by omega))
  have h9 := charge_gas (chargedStore s op) (9 * op) (31 * op + rest) (c1.mono (by omega))
  have ca := entered570_credits s op (31 * op + rest) (hc.mono (by omega))
  have prep := paid_gas (entered570 s op) op 2 (29 * op + rest) (ca.mono (by omega))
  have cp := paid_credits (entered570 s op) op 2 (29 * op + rest) (ca.mono (by omega))
  have body := after568_gas (paid (entered570 s op) op 2) op rest cp
  have entry : (entered570 s op).host.gas.burnt = s.host.gas.burnt + 10 * op := by
    change (chargedStore (chargedStore s op) (9 * op)).host.gas.burnt = _
    rw [h9.1, h1.1]; omega
  refine ⟨?_, body.2.trans (prep.2.trans (h9.2.trans h1.2))⟩
  change (after568 (paid (entered570 s op) op 2) op).host.gas.burnt = _
  rw [body.1, prep.1, entry]; omega


theorem after568_functional_host (s : Store NearState) (op : Nat) :
    {(after568 s op).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [after568, entered568, paid, chargedStore, chargeHost]

theorem after570_functional_host (s : Store NearState) (op : Nat) :
    {(after570 s op).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [after570, bodyAfter570, after568, entered568, entered570, paid, chargedStore, chargeHost]
end WNear.Proofs.DeallocateAlign
