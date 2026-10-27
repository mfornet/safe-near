import Proofs.TotalSupplyEntry

/-! Conditional original-store gas bounds for the complete deployed getter.
The actual method's local callee and structural obligations remain explicit. -/
namespace WNear.Proofs.TotalSupplyBudget
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply WNear.Proofs.TotalSupplyEntry

theorem gas_bounds (cfg : WasmConfig) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (inst : Nat) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hcalls : CallObligations cfg limits (StorePair.voidFrame #[.i32 scratch] inst)
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg (activated cfg s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (activated cfg s) after (StorePair.voidFrame #[.i32 0] inst) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg cost + rest)) :
    final.host.gas.burnt ≤ s.host.gas.burnt + TotalSupply.entryCost cfg cost ∧
    final.host.gas.used ≤ s.host.gas.used + TotalSupply.entryCost cfg cost ∧
    final.host.gas.Credits rest := by
  have hc : s.host.gas.Credits (9 * cfg.regularOpCost + (bodyCost cfg cost + rest)) :=
    hgas.mono (by simp only [TotalSupply.entryCost]; omega)
  have hb := GasCounter.burn_credits s.host.gas (9 * cfg.regularOpCost) (bodyCost cfg cost + rest) hc
  have hwp := TotalSupply.wp_return cfg rest (activated cfg s) final limits inst before after cost steps
    mi globalIndex memoryIndex sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory
    hcalls hboundaries hinv hb.2.2.2
  obtain ⟨remaining, hp, _, hburn, hused, hcredits⟩ := hwp.result
  rw [hp.1, hp.2.1] at hburn hused hcredits
  change final.host.gas.burnt + rest ≤ (activated cfg s).host.gas.burnt + (bodyCost cfg cost + rest) at hburn
  change final.host.gas.used + rest ≤ (activated cfg s).host.gas.used + (bodyCost cfg cost + rest) at hused
  have ha : (activated cfg s).host.gas.burnt = s.host.gas.burnt + 9 * cfg.regularOpCost := hb.2.1
  have hu : (activated cfg s).host.gas.used = s.host.gas.used + 9 * cfg.regularOpCost := by
    simp only [GasCounter.used, activated, chargedStore, chargeHost]
    rw [hb.2.1, hb.2.2.1]
    omega
  refine ⟨?_, ?_, hcredits⟩
  · simp only [TotalSupply.entryCost]; omega
  · simp only [TotalSupply.entryCost]; omega

/-- The checked epilogue changes only gas and the stack global. Local
serialization, return and cleanup effects therefore reach the final store. -/
theorem return_and_storage (cfg : WasmConfig) (initial final : Store NearState)
    (before after : Fin 11 → Store NearState) (scratch pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (copyMemory : Memory) (state : WNear.State)
    (unwrapped returned serialization sliced : Memory)
    (hb : ScalarBoundaries cfg initial final before after scratch globalIndex memoryIndex copyMemory)
    (hr : RepresentationObligations initial.host state scratch pointer length unwrapped returned serialization sliced
      (after 8).host (after 9).host (after 10).host) :
    final.host.returnData = some (WNear.jsonU128 state.totalSupply).toUTF8.toList ∧
    final.host.storage = initial.host.storage := by
  have h := after_cleanup initial.host state scratch pointer length unwrapped returned serialization sliced
    (after 8).host (after 9).host (after 10).host hr
  rw [hb.restored]
  simpa only [setGlobal, StorePairCaller.paid, chargedStore, chargeHost] using h

end WNear.Proofs.TotalSupplyBudget
