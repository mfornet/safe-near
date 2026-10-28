import Proofs.StateDecodeScalarFinalFrame

/-! Intermediate output-stage resources used by the actual scalar tail. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] values updated restored
private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : fields (storeI64 s i a m v)=fields s := rfl
private theorem project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables ∧ t.globals=s.globals :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩

theorem values_stage_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (values wide cfg s p).funcs=(dropCached wide cfg s p).funcs ∧
    (values wide cfg s p).modules=(dropCached wide cfg s p).modules ∧
    (values wide cfg s p).tables=(dropCached wide cfg s p).tables ∧
    (values wide cfg s p).globals=(dropCached wide cfg s p).globals := by
  apply project
  cases wide <;> simp only [values,valuesStore,store64Added,ite_true,Bool.false_eq_true,ite_false,fields_store,fields_paid]

theorem updated_stage_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (updated wide cfg s p).funcs=(values wide cfg s p).funcs ∧
    (updated wide cfg s p).modules=(values wide cfg s p).modules ∧
    (updated wide cfg s p).tables=(values wide cfg s p).tables ∧
    (updated wide cfg s p).globals=(values wide cfg s p).globals := by
  apply project
  simp only [updated,updateStore,store64Local,fields_store,fields_paid]

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem updated_globals (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (updated wide cfg s p).globals=(reserved s cfg.regularOpCost p).globals := by
  rw [(updated_stage_fields wide cfg s p).2.2.2,(values_stage_fields wide cfg s p).2.2.2,dropCached,globals_paid]
  exact (dropped_fields wide cfg s p).2.2.2

theorem updated_global (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (updated wide cfg s p).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
  rw [updated_globals,reserved]
  simp only [setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some]
  rfl

theorem restored_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (restored wide cfg s p).mems[p.memoryIndex]?=some (finalMemory wide p) := by
  have h:=updated_memory wide cfg s p hm
  simp only [restored,finishStore,setGlobal,mems_paid,tagStore]
  apply storeI32_memory
  rw [mems_paid]
  exact h
end WNear.Proofs.StateDecodeScalar
