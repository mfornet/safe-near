import Proofs.AllocateZeroedRetryTailFrame
import Proofs.AllocateRetryFrame
import Proofs.AllocateRetryPayload
import Proofs.AllocateRetryHost

/-! Original resources derive the complete growth-and-zeroed result memory,
its requested zero span, and code/SP frames without future lookups. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] allocated after AllocateRetry.after

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

 theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocated cfg s p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
  unfold allocated allocatedMemory
  apply AllocateRetry.after_memory
  rw [allocateEntered,chargedStore,chargedStore,arguments,mems_paid]
  exact hm
 theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold after finalMemory
  exact tail_memory (allocated cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) (result p) p.size
    (allocated_memory cfg s p hm)

 theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧
    (finalMemory p).byteSize=p.memory.byteSize+(AllocateGrowth.delta (AllocateRetry.growthLayout p.toRetry)).toNat*65536 ∧
    (finalMemory p).max=p.memory.max ∧
    ∀ j, (finalMemory p).read8 j=if (result p).toNat≤j ∧ j<(result p).toNat+p.size.toNat then 0 else (allocatedMemory p).read8 j := by
  have original := AllocateRetry.finalMemory_spec p.toRetry hn
  have fill := ZeroFill.filledMemory_spec (allocatedMemory p) (result p) 0 p.size.toNat original.1
    (AllocateRetry.result_size_span p.toRetry hn) (AllocateRetry.result_width p.toRetry hn)
  exact ⟨fill.1,fill.2.1.trans original.2.1,fill.2.2.1.trans original.2.2,fill.2.2.2⟩
 theorem result_nonzero (p : Layout) (hn : Native p) : result p≠0 :=
  (AllocateRetry.result_nonzero_and_span p.toRetry hn).1

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_entered (s : Store NearState) (op : Nat) : fields (allocateEntered s op)=fields s := rfl
private theorem fields_retry (cfg : WasmConfig) (s : Store NearState) (p : AllocateRetry.Layout) :
    fields (AllocateRetry.after cfg s p)=fields s := by
  have h := AllocateRetry.after_fields cfg s p
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
 theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).funcs=s.funcs ∧ (allocated cfg s p).modules=s.modules ∧ (allocated cfg s p).tables=s.tables := by
  have h : fields (allocated cfg s p)=fields s := by
    rw [allocated,fields_retry,fields_entered,arguments,fields_paid]
  exact ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
 theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables := by
  unfold after
  have h := tail_fields (allocated cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) (result p) p.size
  have a := allocated_fields cfg s p
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.1.trans a.2.2⟩
 theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (allocated cfg s p).globals=s.globals := by
  have gg : (allocateEntered (arguments s cfg.regularOpCost) cfg.regularOpCost).globals[p.globalIndex]?=some p.global := by
    rw [allocateEntered,chargedStore,chargedStore,arguments,globals_paid]
    exact hg
  have h := AllocateRetry.after_globals cfg (allocateEntered (arguments s cfg.regularOpCost) cfg.regularOpCost) p.toRetry gg hv
  simpa only [allocated,allocateEntered,chargedStore,arguments,globals_paid] using h
 theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after cfg s p).globals=s.globals := by
  unfold after
  exact (tail_fields (allocated cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) (result p) p.size).2.2.2.trans
    (allocated_globals cfg s p hg hv)

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_of_mask (seed original actual : NearState)
    (h : {actual with gas:=original.gas,gasProfile:=original.gasProfile}=original) :
    view seed actual=view seed original := by
  have hh := congrArg (view seed) h
  exact hh
private theorem view_retry (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocateRetry.Layout) :
    view seed (AllocateRetry.after cfg s p).host=view seed s.host := by
  exact view_of_mask seed s.host _ (AllocateRetry.after_functional_host cfg s p)
private theorem view_entered (seed : NearState) (s : Store NearState) (op : Nat) :
    view seed (allocateEntered s op).host=view seed s.host := rfl
private theorem view_tail (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :
    view seed (AllocateZeroed.tailAfter s op index memory ptr len).host=view seed s.host := by
  exact view_of_mask seed s.host _ (tail_functional_host s op index memory ptr len)
 theorem allocated_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(allocated cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (allocated cfg s p).host=s.host
  rw [allocated,view_retry,view_entered,arguments,view_paid]
  rfl
 theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p).host=s.host
  rw [after,view_tail]
  exact allocated_functional_host cfg s p
end WNear.Proofs.AllocateZeroedRetry
