import NearLogic.RelaxStep
import NearVM.MeteredInvariant
import NearVM.HostGasLimits

/-!
# `runMetered` under raised gas limits

A run whose gas limits are raised follows the run with the lower limits:
both end in the same state, up to the limits, unless the lower run ends
with a gas failure, a failed charge of the loop or of a host function.
This is how the below-the-bound case of `Refines` reduces to a run with
enough gas.
-/

namespace NearLogic

open Wasm Wasm.Near

/-! ## The loop's charges -/

theorem chargeHost_relax (h : NearState) (k p m : Nat) (hp : h.gas.prepaid ≤ p) (hm : h.gas.maxBurnt ≤ m)
    (hok : (chargeHost h k).2 = none) :
    chargeHost (relax h p m) k = (relax (chargeHost h k).1 p m, none) := by
  unfold chargeHost Near.GasCounter.burn at hok ⊢
  simp only at hok ⊢
  rw [show (relax h p m).gas = { h.gas with prepaid := p, maxBurnt := m } from rfl,
    deduct_relax h.gas k k p m hp hm hok]
  rfl

theorem chargeWasm_relax (r : Machine) (k p m : Nat) (hp : r.store.host.gas.prepaid ≤ p)
    (hm : r.store.host.gas.maxBurnt ≤ m) (hok : (chargeWasm r k).2 = none) :
    chargeWasm (r.relax p m) k = ((chargeWasm r k).1.relax p m, none) := by
  cases r with
  | next c =>
    simp only [StepResult.store] at hp hm
    simp only [chargeWasm, chargeConfig] at hok ⊢
    simp only [StepResult.relax, relaxStore]
    rw [chargeHost_relax _ k p m hp hm hok]
  | done vs s =>
    simp only [StepResult.store] at hp hm
    simp only [chargeWasm] at hok ⊢
    simp only [StepResult.relax, relaxStore]
    rw [chargeHost_relax _ k p m hp hm hok]
  | trap reason s =>
    simp only [StepResult.store] at hp hm
    simp only [chargeWasm] at hok ⊢
    simp only [StepResult.relax, relaxStore]
    rw [chargeHost_relax _ k p m hp hm hok]

theorem chargeConfig_relax (c : Config NearState) (k p m : Nat) (hp : c.store.host.gas.prepaid ≤ p)
    (hm : c.store.host.gas.maxBurnt ≤ m) (hok : (chargeConfig c k).2 = none) :
    chargeConfig { c with store := relaxStore c.store p m } k =
      ({ (chargeConfig c k).1 with store := relaxStore (chargeConfig c k).1.store p m }, none) := by
  simp only [chargeConfig] at hok ⊢
  rw [show (relaxStore c.store p m).host = relax c.store.host p m from rfl, chargeHost_relax _ k p m hp hm hok]
  rfl

theorem frameTransitionGas_relax (cfg : WasmConfig) (c : Config NearState) (r : Machine) (p m : Nat) :
    frameTransitionGas cfg { c with store := relaxStore c.store p m } (r.relax p m) =
      frameTransitionGas cfg c r := by
  cases r <;> rfl

theorem chargeHost_error (h : NearState) (k : Nat) {e : HostError} (he : (chargeHost h k).2 = some e) :
    isGasError e := by
  unfold chargeHost Near.GasCounter.burn at he
  exact deduct_error _ _ _ he

theorem chargeWasm_error (r : Machine) (k : Nat) {e : HostError} (he : (chargeWasm r k).2 = some e) :
    isGasError e := by
  cases r <;> simp only [chargeWasm, chargeConfig] at he <;> exact chargeHost_error _ _ he

/-! ## Runs -/

/-- A run that ended with a gas failure: a failed charge of the loop, or a
trap whose host records a gas error. -/
def GasEnd (r : Machine × Option FunctionCallError) : Prop :=
  (∃ e, r.2 = some (.hostError e) ∧ isGasError e) ∨ (r.2 = none ∧ GasStep r.1)

theorem gasStep_chargeWasm {r : Machine} (k : Nat) (h : GasStep r) : GasStep (chargeWasm r k).1 := by
  obtain ⟨reason, s, e, rfl, hl, he⟩ := h
  exact ⟨reason, _, e, rfl, hl, he⟩

theorem runMetered_gasStep (cfg : WasmConfig) (fuel : Nat) {r : Machine} (h : GasStep r) :
    runMetered cfg fuel r = (r, none) := by
  obtain ⟨reason, s, e, rfl, -, -⟩ := h
  exact runMetered_trapped cfg fuel reason s

theorem step_funcs_eq (c : Config NearState) : (Exec.step c).store.funcs = c.store.funcs :=
  Exec.step_funcs c

/-- **Runs under raised limits.** From a machine whose host keeps the
limits `p0`, `m0` (at most `p`, `m`) and whose host functions respect
raised limits, the run with the limits raised to `p`, `m` ends as the run
with the lower limits, up to the limits, unless the latter ends with a gas
failure. -/
theorem runMetered_relax (cfg : WasmConfig) (p0 m0 p m : Nat) (hp : p0 ≤ p) (hm : m0 ≤ m) (fuel : Nat) :
    ∀ (r : Machine), MachineHostInvariant (GasLimits p0 m0) r → StoreRelaxFns r.store →
      GasEnd (runMetered cfg fuel r) ∨
        runMetered cfg fuel (r.relax p m) = ((runMetered cfg fuel r).1.relax p m, (runMetered cfg fuel r).2) := by
  have hcharge : ∀ (ns : NearState) (cost : Nat), GasLimits p0 m0 ns → GasLimits p0 m0 (chargeHost ns cost).1 :=
    fun ns cost h => by
      have hl := chargeHost_gas_limits ns cost
      exact ⟨hl.1.trans h.1, hl.2.trans h.2⟩
  induction fuel with
  | zero =>
    intro r _ _
    right
    cases r <;> rfl
  | succ fuel ih =>
    intro r hinv hf
    cases r with
    | done vs s => right; rfl
    | trap reason s => right; rfl
    | next c =>
      have hlim : c.store.host.gas.prepaid ≤ p ∧ c.store.host.gas.maxBurnt ≤ m := by
        have := hinv.2; exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
      have hk : nextInstructionGas cfg { c with store := relaxStore c.store p m } = nextInstructionGas cfg c := rfl
      have hcc : ∀ (d : Config NearState) (k : Nat),
          chargeWasm (.next d) k = (.next (chargeConfig d k).1, (chargeConfig d k).2) := fun _ _ => rfl
      show GasEnd (runMetered cfg (fuel + 1) (.next c)) ∨
        runMetered cfg (fuel + 1) (.next { c with store := relaxStore c.store p m }) = _
      unfold runMetered
      rw [hk]
      cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
      | some e =>
        left; left
        simp only [h1]
        exact ⟨e, rfl, chargeHost_error _ _ h1⟩
      | none =>
        rw [chargeConfig_relax c _ p m hlim.1 hlim.2 h1]
        simp only [h1]
        set c1 := (chargeConfig c (nextInstructionGas cfg c)).1 with hc1
        have hinv1 : Exec.ConfigHostInvariant (GasLimits p0 m0) c1 := chargeConfig_hostInvariant hcharge c _ hinv
        have hlim1 : c1.store.host.gas.prepaid ≤ p ∧ c1.store.host.gas.maxBurnt ≤ m := by
          have := hinv1.2; exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
        have hf1 : StoreRelaxFns c1.store := fun a fn h => hf a fn h
        have hinvs : MachineHostInvariant (GasLimits p0 m0) (Exec.step c1) := Wasm.step_hostInvariant hinv1
        have hfs : StoreRelaxFns (Exec.step c1).store := fun a fn h =>
          hf1 a fn (by rw [← step_funcs_eq c1]; exact h)
        rcases step_relax c1 p m hlim1.1 hlim1.2 hf1 with hgs | hst
        · left
          cases h2 : (chargeWasm (Exec.step c1) (frameTransitionGas cfg c1 (Exec.step c1))).2 with
          | some e => left; simp only [h2]; exact ⟨e, rfl, chargeWasm_error _ _ h2⟩
          | none =>
            right
            simp only [h2]
            rw [runMetered_gasStep cfg fuel (gasStep_chargeWasm _ hgs)]
            exact ⟨rfl, gasStep_chargeWasm _ hgs⟩
        · rw [hst, frameTransitionGas_relax]
          cases h2 : (chargeWasm (Exec.step c1) (frameTransitionGas cfg c1 (Exec.step c1))).2 with
          | some e => left; left; simp only [h2]; exact ⟨e, rfl, chargeWasm_error _ _ h2⟩
          | none =>
            have hlims : (Exec.step c1).store.host.gas.prepaid ≤ p ∧
                (Exec.step c1).store.host.gas.maxBurnt ≤ m := by
              have := hinvs.host
              rw [show (Exec.step c1).host = (Exec.step c1).store.host by cases Exec.step c1 <;> rfl] at this
              exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
            rw [chargeWasm_relax _ _ p m hlims.1 hlims.2 h2]
            simp only [h2]
            apply ih
            · exact chargeWasm_hostInvariant hcharge _ _ hinvs
            · intro a fn h
              apply hfs a fn
              cases hs : Exec.step c1 <;> rw [hs] at h <;> simp_all [chargeWasm, chargeConfig, StepResult.store]

end NearLogic
