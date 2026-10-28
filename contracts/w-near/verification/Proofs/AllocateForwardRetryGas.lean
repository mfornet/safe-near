import Proofs.AllocateForwardRetryState

/-! Exact forwarding gas; the symbolic memory-growth fee is included once. -/
namespace WNear.Proofs.AllocateForwardRetry
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] entered153 zeroedAfter after239 callAfter239 called239 after313 callAfter313

private theorem entered_units (s : Store NearState) (op n : Nat) :
    GasUnits s (chargedStore (chargedStore s op) (n*op)) op (1+n) := by
  have one := gasUnits_charge s op 1
  simp only [Nat.one_mul] at one
  exact one.trans (gasUnits_charge (chargedStore s op) op n)

theorem zeroedAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (zeroedAfter cfg s p) ((AllocateZeroedRetry.bodyCost p+11)*cfg.regularOpCost+fee cfg p) := by
  have a : GasUnits s (entered153 s cfg.regularOpCost) cfg.regularOpCost 11 := by
    simpa only [entered153,Nat.reduceAdd] using entered_units s cfg.regularOpCost 10
  have h := (GasCost.of_units a).trans (AllocateZeroedRetry.after_gas cfg (entered153 s cfg.regularOpCost) p)
  have cost : 11*cfg.regularOpCost+(AllocateZeroedRetry.bodyCost p*cfg.regularOpCost+fee cfg p)=
      (AllocateZeroedRetry.bodyCost p+11)*cfg.regularOpCost+fee cfg p := by rw [Nat.add_mul];omega
  simpa only [zeroedAfter,cost] using h

theorem after239_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after239 cfg s p) (cost239 p*cfg.regularOpCost+fee cfg p) := by
  have h := (GasCost.of_units (gasUnits_paid s cfg.regularOpCost 3)).trans
    (zeroedAfter_gas cfg (StorePairCaller.paid s cfg.regularOpCost 3) p)
  have cost : 3*cfg.regularOpCost+((AllocateZeroedRetry.bodyCost p+11)*cfg.regularOpCost+fee cfg p)=
      cost239 p*cfg.regularOpCost+fee cfg p := by simp only [cost239,Nat.add_mul];omega
  simpa only [after239,cost] using h

theorem callAfter239_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (callAfter239 cfg s p) ((cost239 p+10)*cfg.regularOpCost+fee cfg p) := by
  have a : GasUnits s (entered239 s cfg.regularOpCost) cfg.regularOpCost 10 := by
    simpa only [entered239,Nat.reduceAdd] using entered_units s cfg.regularOpCost 9
  have h := (GasCost.of_units a).trans (after239_gas cfg (entered239 s cfg.regularOpCost) p)
  have cost : 10*cfg.regularOpCost+(cost239 p*cfg.regularOpCost+fee cfg p)=(cost239 p+10)*cfg.regularOpCost+fee cfg p := by rw [Nat.add_mul];omega
  simpa only [callAfter239,cost] using h

theorem after313_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after313 cfg s p) (cost313 p*cfg.regularOpCost+fee cfg p) := by
  have a := (GasCost.of_units (gasUnits_paid s cfg.regularOpCost 2)).trans
    (callAfter239_gas cfg (StorePairCaller.paid s cfg.regularOpCost 2) p)
  have aa : GasCost s (called239 cfg s p) (2*cfg.regularOpCost+((cost239 p+10)*cfg.regularOpCost+fee cfg p)) := by simpa only [called239] using a
  have h := aa.trans (GasCost.of_units (gasUnits_paid (called239 cfg s p) cfg.regularOpCost 3))
  have cost : (2*cfg.regularOpCost+((cost239 p+10)*cfg.regularOpCost+fee cfg p))+3*cfg.regularOpCost=
      cost313 p*cfg.regularOpCost+fee cfg p := by simp only [cost313,Nat.add_mul];omega
  simpa only [after313,called239,cost] using h

theorem callAfter313_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (callAfter313 cfg s p) ((cost313 p+11)*cfg.regularOpCost+fee cfg p) := by
  have a : GasUnits s (entered313 s cfg.regularOpCost) cfg.regularOpCost 11 := by
    simpa only [entered313,Nat.reduceAdd] using entered_units s cfg.regularOpCost 10
  have h := (GasCost.of_units a).trans (after313_gas cfg (entered313 s cfg.regularOpCost) p)
  have cost : 11*cfg.regularOpCost+(cost313 p*cfg.regularOpCost+fee cfg p)=(cost313 p+11)*cfg.regularOpCost+fee cfg p := by rw [Nat.add_mul];omega
  simpa only [callAfter313,cost] using h

theorem after239_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (cost239 p*cfg.regularOpCost+fee cfg p+rest)) :
    (after239 cfg s p).host.gas.Credits rest := (after239_gas cfg s p rest hc).2.2

theorem callAfter239_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((cost239 p+10)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter239 cfg s p).host.gas.Credits rest := (callAfter239_gas cfg s p rest hc).2.2

theorem after313_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (cost313 p*cfg.regularOpCost+fee cfg p+rest)) :
    (after313 cfg s p).host.gas.Credits rest := (after313_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateForwardRetry
