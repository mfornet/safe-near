import Proofs.AllocateRawForwardDirectState

/-! Exact ordinary-instruction gas for directly-fitting raw allocation forwarding. -/
namespace WNear.Proofs.AllocateRawForwardDirect
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] entered581 allocatedAfter after236 callAfter236 called236 after310 callAfter310

private theorem entered_units (s : Store NearState) (op n : Nat) :
    GasUnits s (chargedStore (chargedStore s op) (n*op)) op (1+n) := by
  have one := gasUnits_charge s op 1
  simp only [Nat.one_mul] at one
  exact one.trans (gasUnits_charge (chargedStore s op) op n)

theorem allocatedAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (allocatedAfter cfg s p) cfg.regularOpCost 358 := by
  have a : GasUnits s (entered581 s cfg.regularOpCost) cfg.regularOpCost 12 := by
    simpa only [entered581,Nat.reduceAdd] using entered_units s cfg.regularOpCost 11
  have h := a.trans (AllocatePositive.gasUnits_after (entered581 s cfg.regularOpCost) cfg.regularOpCost p)
  simpa only [allocatedAfter,Nat.reduceAdd] using h

theorem after236_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (after236 cfg s p) cfg.regularOpCost (cost236 p) := by
  have h := (gasUnits_paid s cfg.regularOpCost 3).trans (allocatedAfter_gas cfg (StorePairCaller.paid s cfg.regularOpCost 3) p)
  simpa only [after236,cost236,Nat.reduceAdd] using h

theorem callAfter236_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (callAfter236 cfg s p) cfg.regularOpCost (cost236 p+10) := by
  have a : GasUnits s (entered236 s cfg.regularOpCost) cfg.regularOpCost 10 := by
    simpa only [entered236,Nat.reduceAdd] using entered_units s cfg.regularOpCost 9
  have h := a.trans (after236_gas cfg (entered236 s cfg.regularOpCost) p)
  simpa only [callAfter236,Nat.add_comm] using h

theorem after310_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (after310 cfg s p) cfg.regularOpCost (cost310 p) := by
  have a := (gasUnits_paid s cfg.regularOpCost 2).trans (callAfter236_gas cfg (StorePairCaller.paid s cfg.regularOpCost 2) p)
  have aa : GasUnits s (called236 cfg s p) cfg.regularOpCost (2+(cost236 p+10)) := by simpa only [called236] using a
  have h := aa.trans (gasUnits_paid (called236 cfg s p) cfg.regularOpCost 3)
  simpa only [after310,cost310,cost236,Nat.reduceAdd] using h

theorem callAfter310_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (callAfter310 cfg s p) cfg.regularOpCost (cost310 p+11) := by
  have a : GasUnits s (entered310 s cfg.regularOpCost) cfg.regularOpCost 11 := by
    simpa only [entered310,Nat.reduceAdd] using entered_units s cfg.regularOpCost 10
  have h := a.trans (after310_gas cfg (entered310 s cfg.regularOpCost) p)
  simpa only [callAfter310,Nat.add_comm] using h

theorem after236_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (cost236 p*cfg.regularOpCost+rest)) :
    (after236 cfg s p).host.gas.Credits rest := (after236_gas cfg s p rest hc).2.2

theorem callAfter236_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((cost236 p+10)*cfg.regularOpCost+rest)) :
    (callAfter236 cfg s p).host.gas.Credits rest := (callAfter236_gas cfg s p rest hc).2.2

theorem after310_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (cost310 p*cfg.regularOpCost+rest)) :
    (after310 cfg s p).host.gas.Credits rest := (after310_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateRawForwardDirect
