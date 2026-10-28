import Proofs.AllocateVectorCall
import Proofs.AllocateVectorHost
import Proofs.AllocateVectorRecordReadback

/-! Exact final resources of the checked positive686 local call. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] after callAfter finalMemory resultMemory

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  exact after_memory cfg (entered s cfg.regularOpCost) p hm

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables := by
  unfold callAfter
  exact after_fields cfg (entered s cfg.regularOpCost) p

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.outerGlobal) (hv : p.outerGlobal.value=.i32 p.outerSP) :
    (callAfter cfg s p).globals=s.globals := by
  unfold callAfter
  exact after_globals cfg (entered s cfg.regularOpCost) p hn hg hv

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (after cfg s p).host=view seed s.host := by
  have h := congrArg (view seed) (after_functional_host cfg s p)
  exact h

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter cfg s p).host=s.host
  rw [callAfter,view_after]
  rfl

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost p+12)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter cfg s p).host.gas.burnt=s.host.gas.burnt+(bodyCost p+12)*cfg.regularOpCost+fee cfg p ∧
    (callAfter cfg s p).host.gas.promises=s.host.gas.promises ∧ (callAfter cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have a := gasUnits_charge s op 1
  simp only [Nat.one_mul] at a
  have b := a.trans (gasUnits_charge (chargedStore s op) op 11)
  have entry : GasCost s (entered s op) (12*op) := by simpa only [entered,Nat.reduceAdd] using GasCost.of_units b
  have all := entry.trans (after_gas cfg (entered s op) p)
  have ce : 12*op+(bodyCost p*cfg.regularOpCost+fee cfg p)=(bodyCost p+12)*cfg.regularOpCost+fee cfg p := by simp only [op,Nat.add_mul];omega
  rw [ce] at all
  simpa only [callAfter,op,Nat.add_assoc] using all rest hc

theorem callAfter_output (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    ∃ memory, (callAfter cfg s p).mems[p.memoryIndex]?=some memory ∧ memory.wf ∧
      memory.max=p.memory.max ∧ readI32 memory p.out686.toNat=result p ∧
      readI32 memory (p.out686.toNat+4)=p.size := by
  have spec := finalMemory_spec p hn
  exact ⟨finalMemory p,callAfter_memory cfg s p hm,spec.1,spec.2.2.1,spec.2.2.2.1,spec.2.2.2.2.1⟩
end WNear.Proofs.AllocateVector
