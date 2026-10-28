import Proofs.AllocateForwardRetryGas
import Proofs.AllocateZeroedRetryResources

/-! Exact computed forwarding resources for the actual growth-and-zeroed path. -/
namespace WNear.Proofs.AllocateForwardRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_charge (s : Store NearState) (cost : Nat) : fields (chargedStore s cost)=fields s := rfl
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_reset (seed old host : NearState) : view seed (view old host)=view seed host := rfl
private theorem view_rebase (seed base host : NearState) (h : view base host=base) : view seed host=view seed base := by
  have q := congrArg (view seed) h
  simpa only [view_reset] using q
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) : view seed (chargedStore s cost).host=view seed s.host := rfl

attribute [local irreducible] zeroedAfter after239 callAfter239 called239 after313 callAfter313 AllocateZeroedRetry.after

theorem zeroedAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (zeroedAfter cfg s p).mems[p.memoryIndex]?=some (AllocateZeroedRetry.finalMemory p) := by
  unfold zeroedAfter
  apply AllocateZeroedRetry.after_memory
  simpa only [entered153,chargedStore] using hm

theorem callAfter239_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter239 cfg s p).mems[p.memoryIndex]?=some (AllocateZeroedRetry.finalMemory p) := by
  unfold callAfter239 after239
  apply zeroedAfter_memory
  simpa only [mems_paid,entered239,chargedStore] using hm

theorem callAfter313_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter313 cfg s p).mems[p.memoryIndex]?=some (AllocateZeroedRetry.finalMemory p) := by
  unfold callAfter313 after313 called239
  rw [mems_paid]
  apply callAfter239_memory
  simpa only [mems_paid,entered313,chargedStore] using hm

private theorem fields_zeroed (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (zeroedAfter cfg s p)=fields s := by
  have h := AllocateZeroedRetry.after_fields cfg (entered153 s cfg.regularOpCost) p
  have packed : fields (AllocateZeroedRetry.after cfg (entered153 s cfg.regularOpCost) p) =
      fields (entered153 s cfg.regularOpCost) :=
    Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  simpa only [zeroedAfter,fields,entered153,chargedStore] using packed
private theorem fields239 (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (callAfter239 cfg s p)=fields s := by
  rw [callAfter239,after239,fields_zeroed,fields_paid]
  simp only [entered239,fields_charge]
private theorem fields313 (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (callAfter313 cfg s p)=fields s := by
  rw [callAfter313,after313,fields_paid,called239,fields239,fields_paid]
  simp only [entered313,fields_charge]

theorem callAfter239_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter239 cfg s p).funcs=s.funcs ∧ (callAfter239 cfg s p).modules=s.modules ∧ (callAfter239 cfg s p).tables=s.tables := by
  have h := fields239 cfg s p
  exact ⟨congrArg (fun t=>t.1) h,congrArg (fun t=>t.2.1) h,congrArg (fun t=>t.2.2) h⟩
theorem callAfter313_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter313 cfg s p).funcs=s.funcs ∧ (callAfter313 cfg s p).modules=s.modules ∧ (callAfter313 cfg s p).tables=s.tables := by
  have h := fields313 cfg s p
  exact ⟨congrArg (fun t=>t.1) h,congrArg (fun t=>t.2.1) h,congrArg (fun t=>t.2.2) h⟩

private theorem globals_zeroed (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (zeroedAfter cfg s p).globals=s.globals := by
  have h := AllocateZeroedRetry.after_globals cfg (entered153 s cfg.regularOpCost) p (by simpa only [entered153,chargedStore] using hg) hv
  simpa only [zeroedAfter,entered153,chargedStore] using h

theorem callAfter239_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter239 cfg s p).globals=s.globals := by
  unfold callAfter239 after239
  have original : (paid (entered239 s cfg.regularOpCost) cfg.regularOpCost 3).globals[p.globalIndex]?=some p.global := by
    simpa only [globals_paid,entered239,chargedStore] using hg
  rw [globals_zeroed cfg _ p original hv,globals_paid]
  rfl

theorem callAfter313_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter313 cfg s p).globals=s.globals := by
  unfold callAfter313 after313 called239
  rw [globals_paid]
  have original : (paid (entered313 s cfg.regularOpCost) cfg.regularOpCost 2).globals[p.globalIndex]?=some p.global := by
    simpa only [globals_paid,entered313,chargedStore] using hg
  rw [callAfter239_globals cfg _ p original hv,globals_paid]
  rfl

private theorem view_zeroed (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) : view seed (zeroedAfter cfg s p).host=view seed s.host := by
  have h : view (entered153 s cfg.regularOpCost).host (AllocateZeroedRetry.after cfg (entered153 s cfg.regularOpCost) p).host=(entered153 s cfg.regularOpCost).host :=
    AllocateZeroedRetry.after_functional_host cfg (entered153 s cfg.regularOpCost) p
  have rebase := view_rebase seed (entered153 s cfg.regularOpCost).host (AllocateZeroedRetry.after cfg (entered153 s cfg.regularOpCost) p).host h
  simpa only [zeroedAfter,entered153,view_charge] using rebase
private theorem view239 (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) : view seed (callAfter239 cfg s p).host=view seed s.host := by
  rw [callAfter239,after239,view_zeroed,view_paid]
  simp only [entered239,view_charge]

theorem callAfter239_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter239 cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := view239 s.host cfg s p

theorem callAfter313_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter313 cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter313 cfg s p).host=s.host
  rw [callAfter313,after313,view_paid,called239,view239,view_paid]
  simp only [entered313,view_charge]
  rfl
end WNear.Proofs.AllocateForwardRetry
