import Proofs.AllocateRawForwardDirectGas
import Proofs.AllocatePositiveResources

/-! Exact computed forwarding resources for the actual nonzeroing directly-fitting path. -/
namespace WNear.Proofs.AllocateRawForwardDirect
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

attribute [local irreducible] allocatedAfter after236 callAfter236 called236 after310 callAfter310 AllocatePositive.after

theorem allocatedAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocatedAfter cfg s p).mems[p.memoryIndex]?=some (AllocatePositive.finalMemory p) := by
  unfold allocatedAfter
  apply AllocatePositive.after_memory
  simpa only [entered581,chargedStore] using hm

theorem callAfter236_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter236 cfg s p).mems[p.memoryIndex]?=some (AllocatePositive.finalMemory p) := by
  unfold callAfter236 after236
  apply allocatedAfter_memory
  simpa only [mems_paid,entered236,chargedStore] using hm

theorem callAfter310_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter310 cfg s p).mems[p.memoryIndex]?=some (AllocatePositive.finalMemory p) := by
  unfold callAfter310 after310 called236
  rw [mems_paid]
  apply callAfter236_memory
  simpa only [mems_paid,entered310,chargedStore] using hm

private theorem fields_zeroed (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (allocatedAfter cfg s p)=fields s := by
  have h := AllocatePositive.after_fields (entered581 s cfg.regularOpCost) cfg.regularOpCost p
  have packed : fields (AllocatePositive.after (entered581 s cfg.regularOpCost) cfg.regularOpCost p) =
      fields (entered581 s cfg.regularOpCost) :=
    Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  simpa only [allocatedAfter,fields,entered581,chargedStore] using packed
private theorem fields236 (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (callAfter236 cfg s p)=fields s := by
  rw [callAfter236,after236,fields_zeroed,fields_paid]
  simp only [entered236,fields_charge]
private theorem fields310 (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (callAfter310 cfg s p)=fields s := by
  rw [callAfter310,after310,fields_paid,called236,fields236,fields_paid]
  simp only [entered310,fields_charge]

theorem callAfter236_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter236 cfg s p).funcs=s.funcs ∧ (callAfter236 cfg s p).modules=s.modules ∧ (callAfter236 cfg s p).tables=s.tables := by
  have h := fields236 cfg s p
  exact ⟨congrArg (fun t=>t.1) h,congrArg (fun t=>t.2.1) h,congrArg (fun t=>t.2.2) h⟩
theorem callAfter310_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter310 cfg s p).funcs=s.funcs ∧ (callAfter310 cfg s p).modules=s.modules ∧ (callAfter310 cfg s p).tables=s.tables := by
  have h := fields310 cfg s p
  exact ⟨congrArg (fun t=>t.1) h,congrArg (fun t=>t.2.1) h,congrArg (fun t=>t.2.2) h⟩

private theorem globals_zeroed (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (allocatedAfter cfg s p).globals=s.globals := by
  have h := AllocatePositive.after_globals (entered581 s cfg.regularOpCost) cfg.regularOpCost p (by simpa only [entered581,chargedStore] using hg) hv
  simpa only [allocatedAfter,entered581,chargedStore] using h

theorem callAfter236_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter236 cfg s p).globals=s.globals := by
  unfold callAfter236 after236
  have original : (paid (entered236 s cfg.regularOpCost) cfg.regularOpCost 3).globals[p.globalIndex]?=some p.global := by
    simpa only [globals_paid,entered236,chargedStore] using hg
  rw [globals_zeroed cfg _ p original hv,globals_paid]
  rfl

theorem callAfter310_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter310 cfg s p).globals=s.globals := by
  unfold callAfter310 after310 called236
  rw [globals_paid]
  have original : (paid (entered310 s cfg.regularOpCost) cfg.regularOpCost 2).globals[p.globalIndex]?=some p.global := by
    simpa only [globals_paid,entered310,chargedStore] using hg
  rw [callAfter236_globals cfg _ p original hv,globals_paid]
  rfl

private theorem view_zeroed (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) : view seed (allocatedAfter cfg s p).host=view seed s.host := by
  have h : view (entered581 s cfg.regularOpCost).host (AllocatePositive.after (entered581 s cfg.regularOpCost) cfg.regularOpCost p).host=(entered581 s cfg.regularOpCost).host :=
    AllocatePositive.after_functional_host (entered581 s cfg.regularOpCost) cfg.regularOpCost p
  have rebase := view_rebase seed (entered581 s cfg.regularOpCost).host (AllocatePositive.after (entered581 s cfg.regularOpCost) cfg.regularOpCost p).host h
  simpa only [allocatedAfter,entered581,view_charge] using rebase
private theorem view236 (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) : view seed (callAfter236 cfg s p).host=view seed s.host := by
  rw [callAfter236,after236,view_zeroed,view_paid]
  simp only [entered236,view_charge]

theorem callAfter236_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter236 cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := view236 s.host cfg s p

theorem callAfter310_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter310 cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter310 cfg s p).host=s.host
  rw [callAfter310,after310,view_paid,called236,view236,view_paid]
  simp only [entered310,view_charge]
  rfl
end WNear.Proofs.AllocateRawForwardDirect
