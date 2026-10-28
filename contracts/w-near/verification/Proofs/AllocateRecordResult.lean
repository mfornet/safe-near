import Proofs.AllocateRecordCall

/-! Canonical two-word output and original SP/functional-resource frame of the
complete typed689 call. Output aliases retain the exact sequential memory. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (gasUnits_charge)
open AllocateGrowth (GasCost)
attribute [local irreducible] allocated selected after callAfter

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem record_globals (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32) :
    (recordStore s op index memory out pointer size).globals=s.globals := by
  rw [recordStore,storeI32_globals,globals_paid,storeI32_globals,globals_paid]
 theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (allocated cfg s p).globals=s.globals := by
  have gg : (paid s cfg.regularOpCost 8).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  have h := AllocateForwardRetry.callAfter313_globals cfg (paid s cfg.regularOpCost 8) p.toZeroed gg hv
  simpa only [allocated,globals_paid] using h
 theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after cfg s p).globals=s.globals := by
  rw [after,record_globals,selected,globals_paid]
  exact allocated_globals cfg s p hg hv

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_of_mask (seed original actual : NearState)
    (h : {actual with gas:=original.gas,gasProfile:=original.gasProfile}=original) :
    view seed actual=view seed original := by
  have hh := congrArg (view seed) h
  exact hh
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    view seed (storeI32 s index address memory v).host=view seed s.host := rfl
private theorem view313 (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocateZeroedRetry.Layout) :
    view seed (AllocateForwardRetry.callAfter313 cfg s p).host=view seed s.host :=
  view_of_mask seed s.host _ (AllocateForwardRetry.callAfter313_functional_host cfg s p)
private theorem view_record (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32) :
    view seed (recordStore s op index memory out pointer size).host=view seed s.host := by
  rw [recordStore,view_store,view_paid,view_store,view_paid]
private theorem view_allocated (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (allocated cfg s p).host=view seed s.host := by
  rw [allocated,view313,view_paid]
 theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p).host=s.host
  rw [after,view_record,selected,view_paid,view_allocated]
  rfl

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
private theorem view_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (after cfg s p).host=view seed s.host :=
  view_of_mask seed s.host _ (after_functional_host cfg s p)
 theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter cfg s p).host=s.host
  rw [callAfter,view_after]
  rfl
 theorem callAfter_output (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (finalMemory p) ∧
    readI32 (finalMemory p) p.out.toNat=result p ∧ readI32 (finalMemory p) (p.out.toNat+4)=p.size := by
  have h := finalMemory_spec p hn
  exact ⟨callAfter_memory cfg s p hm,h.2.2.2.1,h.2.2.2.2.1⟩

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
end WNear.Proofs.AllocateRecord
