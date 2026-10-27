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

theorem frameTransitionGas_relax (cfg : WasmConfig) (c : Config NearState) (r : Machine) (p m : Nat) :
    frameTransitionGas cfg { c with store := relaxStore c.store p m } (r.relax p m) =
      frameTransitionGas cfg c r := by
  cases r <;> rfl

end NearLogic
