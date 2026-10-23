import NearVM.MeteredInvariant

namespace Wasm.Near

namespace GasCounter

/-- The VM counter fits both its current execution and prepaid limits. -/
def Bounded (g : GasCounter) : Prop := g.burnt ≤ g.maxBurnt ∧ g.used ≤ g.prepaid

/-- Every charge produces a bounded counter, including saturation on failure. -/
theorem deduct_bounded (g : GasCounter) (burn use : Nat) : (g.deduct burn use).1.Bounded := by
  unfold deduct
  dsimp only
  split
  · rename_i h
    exact h
  · constructor
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

@[simp] theorem deduct_limits (g : GasCounter) (burn use : Nat) :
    (g.deduct burn use).1.prepaid = g.prepaid ∧ (g.deduct burn use).1.maxBurnt = g.maxBurnt := by
  unfold deduct
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- Valid charges increase used gas by exactly `use` on success. -/
theorem deduct_success (g : GasCounter) (burn use : Nat) (horder : burn ≤ use)
    (hok : (g.deduct burn use).2 = none) :
    (g.deduct burn use).1.burnt = g.burnt + burn ∧
    (g.deduct burn use).1.promises = g.promises + (use - burn) ∧
    (g.deduct burn use).1.used = g.used + use := by
  unfold deduct at hok ⊢
  dsimp only at hok ⊢
  split
  · exact ⟨rfl, rfl, by dsimp only [used]; omega⟩
  · rename_i h
    rw [ite_eq_right h] at hok
    contradiction

/-- Failure drops promise gas and reports the per-call limit first. -/
theorem deduct_failure (g : GasCounter) (burn use : Nat)
    (hfail : ¬ (g.burnt + burn ≤ g.maxBurnt ∧ g.burnt + burn + (g.promises + (use - burn)) ≤ g.prepaid)) :
    (g.deduct burn use).1.burnt = min (g.burnt + burn) (min g.prepaid g.maxBurnt) ∧
    (g.deduct burn use).1.promises = 0 ∧
    (g.deduct burn use).2 = some (if g.burnt + burn > g.maxBurnt then .gasLimitExceeded else .gasExceeded) := by
  simp [deduct, hfail]

/-- Charging a valid counter never decreases irreversible burn. -/
theorem deduct_burnt_mono (g : GasCounter) (burn use : Nat) (h : g.Bounded) :
    g.burnt ≤ (g.deduct burn use).1.burnt := by
  unfold deduct
  dsimp only
  split
  · exact Nat.le_add_right _ _
  · have hp : g.burnt ≤ g.prepaid := by have hu := h.2; unfold used at hu; omega
    exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, Nat.le_min.mpr ⟨hp, h.1⟩⟩

theorem burn_bounded (g : GasCounter) (n : Nat) : (g.burn n).1.Bounded := deduct_bounded _ _ _
theorem prepay_bounded (g : GasCounter) (n : Nat) : (g.prepay n).1.Bounded := deduct_bounded _ _ _
theorem payAction_bounded (g : GasCounter) (burn use : Nat) : (g.payAction burn use).1.Bounded :=
  deduct_bounded _ _ _

end GasCounter

/-- Host charging enforces the current gas limits for every charge variant. -/
theorem applyCharge_gas_bounded (ns : NearState) (charge : Charge) :
    (applyCharge ns charge).1.gas.Bounded := by
  cases charge <;> exact GasCounter.deduct_bounded _ _ _

/-- Charges never rewrite the limits supplied by the call context. -/
theorem applyCharge_gas_limits (ns : NearState) (charge : Charge) :
    (applyCharge ns charge).1.gas.prepaid = ns.gas.prepaid ∧
    (applyCharge ns charge).1.gas.maxBurnt = ns.gas.maxBurnt := by
  cases charge <;> exact GasCounter.deduct_limits _ _ _

/-- Lists of host charges preserve bounds, including early error exits. -/
theorem applyCharges_gas_bounded (ns : NearState) (charges : List Charge) (h : ns.gas.Bounded) :
    (applyCharges ns charges).1.gas.Bounded := by
  induction charges generalizing ns with
  | nil => exact h
  | cons charge charges ih =>
    have hp := applyCharge_gas_bounded ns charge
    unfold applyCharges
    cases hc : applyCharge ns charge with
    | mk paid error =>
      rw [hc] at hp
      cases error with
      | none => exact ih paid hp
      | some error => exact hp

theorem applyCharges_gas_limits (ns : NearState) (charges : List Charge) :
    (applyCharges ns charges).1.gas.prepaid = ns.gas.prepaid ∧
    (applyCharges ns charges).1.gas.maxBurnt = ns.gas.maxBurnt := by
  induction charges generalizing ns with
  | nil => exact ⟨rfl, rfl⟩
  | cons charge charges ih =>
    have hp := applyCharge_gas_limits ns charge
    unfold applyCharges
    cases hc : applyCharge ns charge with
    | mk paid error =>
      rw [hc] at hp
      cases error with
      | none => exact ⟨(ih paid).1.trans hp.1, (ih paid).2.trans hp.2⟩
      | some error => exact hp

/-- Initial counters are bounded for ordinary and view calls alike. -/
theorem VMContext.toNearState_gas_bounded (ctx : VMContext) (cfg : RuntimeConfig)
    (storage : List (Bytes × Bytes)) : (ctx.toNearState cfg storage).gas.Bounded := by
  simp [VMContext.toNearState, GasCounter.Bounded, GasCounter.used]

/-- Wasm instruction/frame charging enforces the same counter bounds. -/
theorem chargeHost_gas_bounded (ns : NearState) (cost : Nat) :
    (chargeHost ns cost).1.gas.Bounded :=
  GasCounter.deduct_bounded _ _ _

theorem chargeHost_gas_limits (ns : NearState) (cost : Nat) :
    (chargeHost ns cost).1.gas.prepaid = ns.gas.prepaid ∧
    (chargeHost ns cost).1.gas.maxBurnt = ns.gas.maxBurnt :=
  GasCounter.deduct_limits _ _ _

theorem chargeWasm_gas_bounded (m : Machine) (cost : Nat) :
    (chargeWasm m cost).1.host.gas.Bounded := by
  cases m <;> exact chargeHost_gas_bounded _ _

theorem chargeWasm_gas_limits (m : Machine) (cost : Nat) :
    (chargeWasm m cost).1.host.gas.prepaid = m.host.gas.prepaid ∧
    (chargeWasm m cost).1.host.gas.maxBurnt = m.host.gas.maxBurnt := by
  cases m <;> exact chargeHost_gas_limits _ _

/-- Every executable metered-loop exit has bounded gas. The theorem covers
terminal states, fuel exhaustion and gas exhaustion. It bounds the final
counter against its own limits; fixed input-budget preservation is a separate
host-state invariant. -/
theorem runMetered_gas_bounded (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : m.host.gas.Bounded) : (runMetered cfg fuel m).1.host.gas.Bounded := by
  induction fuel generalizing m with
  | zero => cases m <;> simpa only [runMetered] using h
  | succ fuel ih =>
    cases m with
    | done values store => simpa only [runMetered] using h
    | trap reason store => simpa only [runMetered] using h
    | next c =>
      simp only [runMetered]
      split
      · exact chargeHost_gas_bounded _ _
      · split
        · exact chargeWasm_gas_bounded _ _
        · exact ih _ (chargeWasm_gas_bounded _ _)

/-- Fixed call-budget bounds compose with the runtime's host invariant.
The host-invariant premise requires imported functions to preserve the limits;
this does not assume that they already preserve the desired gas bounds. -/
theorem runMetered_fixed_budget (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (prepaid maxBurnt : Nat)
    (hlimits : MachineHostInvariant
      (fun ns : NearState => ns.gas.prepaid = prepaid ∧ ns.gas.maxBurnt = maxBurnt) m)
    (hbound : m.host.gas.Bounded) :
    let gas := (runMetered cfg fuel m).1.host.gas
    gas.burnt ≤ maxBurnt ∧ gas.used ≤ prepaid := by
  have hl := runMetered_hostInvariant
    (fun ns : NearState => ns.gas.prepaid = prepaid ∧ ns.gas.maxBurnt = maxBurnt)
    (by
      intro current cost h
      have hp := chargeHost_gas_limits current cost
      exact ⟨hp.1.trans h.1, hp.2.trans h.2⟩) cfg fuel m hlimits
  have hb := runMetered_gas_bounded cfg fuel m hbound
  exact ⟨by simpa only [hl.host.2] using hb.1, by simpa only [hl.host.1] using hb.2⟩

end Wasm.Near
