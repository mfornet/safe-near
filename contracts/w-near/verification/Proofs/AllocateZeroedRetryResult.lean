import Proofs.AllocateZeroedRetryCall

/-! Exact typed153 growth/retry result: grown, zeroed memory and original
functional resources, with ordinary gas and linear growth fee kept separate. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (gasUnits_charge)
open AllocateGrowth (GasCost)
attribute [local irreducible] callAfter after

 theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  exact after_memory cfg (entered s cfg.regularOpCost) p hm
 theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables := by
  unfold callAfter
  exact after_fields cfg (entered s cfg.regularOpCost) p
 theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p).globals=s.globals := by
  unfold callAfter
  exact after_globals cfg (entered s cfg.regularOpCost) p hg hv

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_of_mask (seed original actual : NearState)
    (h : {actual with gas:=original.gas,gasProfile:=original.gasProfile}=original) :
    view seed actual=view seed original := by
  have hh := congrArg (view seed) h
  exact hh
private theorem view_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (after cfg s p).host=view seed s.host :=
  view_of_mask seed s.host _ (after_functional_host cfg s p)
 theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter cfg s p).host=s.host
  rw [callAfter,view_after]
  rfl

 theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost p+11)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter cfg s p).host.gas.burnt=s.host.gas.burnt+(bodyCost p+11)*cfg.regularOpCost+fee cfg p ∧
    (callAfter cfg s p).host.gas.promises=s.host.gas.promises ∧ (callAfter cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have a := gasUnits_charge s op 1
  simp only [Nat.one_mul] at a
  have b := a.trans (gasUnits_charge (chargedStore s op) op 10)
  have entry : GasCost s (entered s op) (11*op) := by
    simpa only [entered,Nat.reduceAdd] using GasCost.of_units b
  have all := entry.trans (after_gas cfg (entered s op) p)
  have ce : 11*op+(bodyCost p*cfg.regularOpCost+fee cfg p)=(bodyCost p+11)*cfg.regularOpCost+fee cfg p := by
    simp only [op,Nat.add_mul];omega
  rw [ce] at all
  have h := all rest hc
  simpa only [callAfter,op,Nat.add_assoc] using h
end WNear.Proofs.AllocateZeroedRetry
