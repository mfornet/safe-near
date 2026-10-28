import Proofs.AllocateRawForwardState

/-! Exact forwarding gas; the symbolic memory-growth fee is included once. -/
namespace WNear.Proofs.AllocateRawForward
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] entered581 allocatedAfter after236 callAfter236 called236 after310 callAfter310

private theorem entered_units (s : Store NearState) (op n : Nat) :
    GasUnits s (chargedStore (chargedStore s op) (n*op)) op (1+n) := by
  have one := gasUnits_charge s op 1
  simp only [Nat.one_mul] at one
  exact one.trans (gasUnits_charge (chargedStore s op) op n)

theorem allocatedAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (allocatedAfter cfg s p) ((591+12)*cfg.regularOpCost+fee cfg p) := by
  have a : GasUnits s (entered581 s cfg.regularOpCost) cfg.regularOpCost 12 := by
    simpa only [entered581,Nat.reduceAdd] using entered_units s cfg.regularOpCost 11
  have h := (GasCost.of_units a).trans (AllocateRetry.after_gas cfg (entered581 s cfg.regularOpCost) p)
  have cost : 12*cfg.regularOpCost+(591*cfg.regularOpCost+fee cfg p)=
      (591+12)*cfg.regularOpCost+fee cfg p := by omega
  simpa only [allocatedAfter,cost] using h

theorem after236_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after236 cfg s p) (cost236 p*cfg.regularOpCost+fee cfg p) := by
  have h := (GasCost.of_units (gasUnits_paid s cfg.regularOpCost 3)).trans
    (allocatedAfter_gas cfg (StorePairCaller.paid s cfg.regularOpCost 3) p)
  have cost : 3*cfg.regularOpCost+((591+12)*cfg.regularOpCost+fee cfg p)=
      cost236 p*cfg.regularOpCost+fee cfg p := by simp only [cost236,Nat.add_mul];omega
  simpa only [after236,cost] using h

theorem callAfter236_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (callAfter236 cfg s p) ((cost236 p+10)*cfg.regularOpCost+fee cfg p) := by
  have a : GasUnits s (entered236 s cfg.regularOpCost) cfg.regularOpCost 10 := by
    simpa only [entered236,Nat.reduceAdd] using entered_units s cfg.regularOpCost 9
  have h := (GasCost.of_units a).trans (after236_gas cfg (entered236 s cfg.regularOpCost) p)
  have cost : 10*cfg.regularOpCost+(cost236 p*cfg.regularOpCost+fee cfg p)=(cost236 p+10)*cfg.regularOpCost+fee cfg p := by rw [Nat.add_mul];omega
  simpa only [callAfter236,cost] using h

theorem after310_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after310 cfg s p) (cost310 p*cfg.regularOpCost+fee cfg p) := by
  have a := (GasCost.of_units (gasUnits_paid s cfg.regularOpCost 2)).trans
    (callAfter236_gas cfg (StorePairCaller.paid s cfg.regularOpCost 2) p)
  have aa : GasCost s (called236 cfg s p) (2*cfg.regularOpCost+((cost236 p+10)*cfg.regularOpCost+fee cfg p)) := by simpa only [called236] using a
  have h := aa.trans (GasCost.of_units (gasUnits_paid (called236 cfg s p) cfg.regularOpCost 3))
  have cost : (2*cfg.regularOpCost+((cost236 p+10)*cfg.regularOpCost+fee cfg p))+3*cfg.regularOpCost=
      cost310 p*cfg.regularOpCost+fee cfg p := by simp only [cost310,Nat.add_mul];omega
  simpa only [after310,called236,cost] using h

theorem callAfter310_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (callAfter310 cfg s p) ((cost310 p+11)*cfg.regularOpCost+fee cfg p) := by
  have a : GasUnits s (entered310 s cfg.regularOpCost) cfg.regularOpCost 11 := by
    simpa only [entered310,Nat.reduceAdd] using entered_units s cfg.regularOpCost 10
  have h := (GasCost.of_units a).trans (after310_gas cfg (entered310 s cfg.regularOpCost) p)
  have cost : 11*cfg.regularOpCost+(cost310 p*cfg.regularOpCost+fee cfg p)=(cost310 p+11)*cfg.regularOpCost+fee cfg p := by rw [Nat.add_mul];omega
  simpa only [callAfter310,cost] using h

theorem after236_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (cost236 p*cfg.regularOpCost+fee cfg p+rest)) :
    (after236 cfg s p).host.gas.Credits rest := (after236_gas cfg s p rest hc).2.2

theorem callAfter236_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((cost236 p+10)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter236 cfg s p).host.gas.Credits rest := (callAfter236_gas cfg s p rest hc).2.2

theorem after310_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (cost310 p*cfg.regularOpCost+fee cfg p+rest)) :
    (after310 cfg s p).host.gas.Credits rest := (after310_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateRawForward
