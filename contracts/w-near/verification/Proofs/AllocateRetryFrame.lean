import Proofs.AllocateRetryState
import Proofs.AllocatePositiveResources

/-! Original memory and installed-code/global frames of actual581 growth/retry. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] reserved prefixed firstAttempt firstMiss beforeGrow grown checked oldLinked relinked retried found updated after
  AllocateGrowth.callAfter AllocateFlagged.callAfter AllocateEmpty.callAfter readI32 writeI32

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems := rfl

theorem prefixed_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (prefixed s op p).mems[p.memoryIndex]?=some (savedMemory p) := by
  simpa only [prefixed,savedMemory] using AllocatePositive.prefixed_memory s op p.toLayout hm

theorem beforeGrow_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (beforeGrow s op p).mems[p.memoryIndex]?=some (savedMemory p) := by
  rw [beforeGrow,mems_paid,firstMiss,mems_paid,firstAttempt,(AllocateEmpty.callAfter_frame _ op).1,mems_paid]
  exact prefixed_memory s op p hm

theorem grown_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (grown cfg s p).mems[p.memoryIndex]?=some (AllocateGrowth.finalMemory (growthLayout p)) := by
  unfold grown
  exact AllocateGrowth.callAfter_memory cfg (beforeGrow s cfg.regularOpCost p) (growthLayout p)
    (beforeGrow_memory s cfg.regularOpCost p hm)

theorem checked_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (checked cfg s p).mems[p.memoryIndex]?=some (AllocateGrowth.finalMemory (growthLayout p)) := by
  rw [checked,mems_paid]
  exact grown_memory cfg s p hm

theorem oldLinked_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (oldLinked cfg s p).mems[p.memoryIndex]?=some
      (writeI32 (AllocateGrowth.finalMemory (growthLayout p)) ((AllocateGrowth.header (growthLayout p)).toNat+8)
        (readI32 (AllocateGrowth.finalMemory (growthLayout p)) ((scratch p).toNat+12))) := by
  unfold oldLinked
  apply storeI32_memory
  rw [mems_paid]
  exact checked_memory cfg s p hm

theorem relinked_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (relinked cfg s p).mems[p.memoryIndex]?=some (secondLayout p).memory := by
  unfold relinked
  apply storeI32_memory
  rw [mems_paid]
  exact oldLinked_memory cfg s p hm

theorem retried_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (retried cfg s p).mems[p.memoryIndex]?=some (searchedMemory p) := by
  unfold retried searchedMemory
  apply AllocateFlagged.callAfter_memory
  rw [mems_paid]
  exact relinked_memory cfg s p hm

theorem found_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (found cfg s p).mems[p.memoryIndex]?=some (searchedMemory p) := by
  rw [found,mems_paid]
  exact retried_memory cfg s p hm

theorem updated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (updated cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold updated finalMemory
  apply storeI32_memory
  rw [mems_paid]
  exact found_memory cfg s p hm

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  rw [after,mems_paid,mems_global,mems_paid]
  exact updated_memory cfg s p hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s := rfl
private theorem fields_global (s : Store NearState) (i : Nat) (v : Value) : fields (setGlobal s i v)=fields s := rfl
private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables := by
  simpa only [fields,Prod.mk.injEq] using h
private theorem fields_prefixed (s : Store NearState) (op : Nat) (p : Layout) : fields (prefixed s op p)=fields s := by
  have h := AllocatePositive.prefixed_fields s op p.toLayout
  simpa only [prefixed,fields,Prod.mk.injEq] using h
private theorem fields_empty (s : Store NearState) (op : Nat) : fields (AllocateEmpty.callAfter s op)=fields s := by
  have h := AllocateEmpty.callAfter_frame s op
  exact Prod.ext h.2.2.1 (Prod.ext h.2.1 h.2.2.2.2.1)
private theorem fields_growth (cfg : WasmConfig) (s : Store NearState) (p : AllocateGrowth.Layout) : fields (AllocateGrowth.callAfter cfg s p)=fields s := by
  have h := AllocateGrowth.callAfter_fields cfg s p
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2.2)
private theorem fields_flagged (s : Store NearState) (op : Nat) (p : AllocateSearch.Layout) : fields (AllocateFlagged.callAfter s op p)=fields s := by
  have h := AllocateFlagged.callAfter_fields s op p
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2.1)

private theorem fields_beforeGrow (s : Store NearState) (op : Nat) (p : Layout) : fields (beforeGrow s op p)=fields s := by
  rw [beforeGrow,fields_paid,firstMiss,fields_paid,firstAttempt,fields_empty,fields_paid,fields_prefixed]

theorem beforeGrow_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (beforeGrow s op p).funcs=s.funcs ∧ (beforeGrow s op p).modules=s.modules ∧ (beforeGrow s op p).tables=s.tables :=
  fields_project s _ (fields_beforeGrow s op p)

private theorem fields_grown (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (grown cfg s p)=fields s := by
  rw [grown,fields_growth,fields_beforeGrow]

theorem grown_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (grown cfg s p).funcs=s.funcs ∧ (grown cfg s p).modules=s.modules ∧ (grown cfg s p).tables=s.tables :=
  fields_project s _ (fields_grown cfg s p)

private theorem fields_checked (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (checked cfg s p)=fields s := by
  rw [checked,fields_paid,fields_grown]

theorem checked_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (checked cfg s p).funcs=s.funcs ∧ (checked cfg s p).modules=s.modules ∧ (checked cfg s p).tables=s.tables :=
  fields_project s _ (fields_checked cfg s p)

private theorem fields_oldLinked (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (oldLinked cfg s p)=fields s := by
  rw [oldLinked,fields_store,fields_paid,fields_checked]

theorem oldLinked_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (oldLinked cfg s p).funcs=s.funcs ∧ (oldLinked cfg s p).modules=s.modules ∧ (oldLinked cfg s p).tables=s.tables :=
  fields_project s _ (fields_oldLinked cfg s p)

private theorem fields_relinked (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (relinked cfg s p)=fields s := by
  rw [relinked,fields_store,fields_paid,fields_oldLinked]

theorem relinked_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (relinked cfg s p).funcs=s.funcs ∧ (relinked cfg s p).modules=s.modules ∧ (relinked cfg s p).tables=s.tables :=
  fields_project s _ (fields_relinked cfg s p)

private theorem fields_retried (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (retried cfg s p)=fields s := by
  rw [retried,fields_flagged,fields_paid,fields_relinked]

theorem retried_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (retried cfg s p).funcs=s.funcs ∧ (retried cfg s p).modules=s.modules ∧ (retried cfg s p).tables=s.tables :=
  fields_project s _ (fields_retried cfg s p)

private theorem fields_found (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (found cfg s p)=fields s := by
  rw [found,fields_paid,fields_retried]

theorem found_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (found cfg s p).funcs=s.funcs ∧ (found cfg s p).modules=s.modules ∧ (found cfg s p).tables=s.tables :=
  fields_project s _ (fields_found cfg s p)

private theorem fields_updated (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (updated cfg s p)=fields s := by
  rw [updated,fields_store,fields_paid,fields_found]

theorem updated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (updated cfg s p).funcs=s.funcs ∧ (updated cfg s p).modules=s.modules ∧ (updated cfg s p).tables=s.tables :=
  fields_project s _ (fields_updated cfg s p)

private theorem fields_after (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (after cfg s p)=fields s := by
  rw [after,fields_paid,fields_global,fields_paid,fields_updated]

theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables :=
  fields_project s _ (fields_after cfg s p)

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : (storeI32 s i a m v).globals=s.globals := rfl
private theorem globals_empty (s : Store NearState) (op : Nat) : (AllocateEmpty.callAfter s op).globals=s.globals :=
  (AllocateEmpty.callAfter_frame s op).2.2.2.1
private theorem globals_growth (cfg : WasmConfig) (s : Store NearState) (p : AllocateGrowth.Layout) :
    (AllocateGrowth.callAfter cfg s p).globals=s.globals := (AllocateGrowth.callAfter_fields cfg s p).2.2.1
private theorem globals_flagged (s : Store NearState) (op : Nat) (p : AllocateSearch.Layout) :
    (AllocateFlagged.callAfter s op p).globals=s.globals := (AllocateFlagged.callAfter_fields s op p).2.2.2

theorem prefixed_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (prefixed s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  simpa only [prefixed,scratch] using AllocatePositive.prefixed_globals s op p.toLayout

theorem beforeGrow_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (beforeGrow s op p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [beforeGrow,globals_paid,firstMiss,globals_paid,firstAttempt,globals_empty,globals_paid,prefixed_globals]

theorem grown_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (grown cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [grown,globals_growth,beforeGrow_globals]

theorem checked_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (checked cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [checked,globals_paid,grown_globals]

theorem oldLinked_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (oldLinked cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [oldLinked,globals_store,globals_paid,checked_globals]

theorem relinked_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (relinked cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [relinked,globals_store,globals_paid,oldLinked_globals]

theorem retried_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (retried cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [retried,globals_flagged,globals_paid,relinked_globals]

theorem found_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (found cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [found,globals_paid,retried_globals]

theorem updated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (updated cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  rw [updated,globals_store,globals_paid,found_globals]

theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after cfg s p).globals=s.globals := by
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  rw [after,globals_paid]
  simp only [setGlobal,globals_paid]
  rw [updated_globals]
  simpa only [setGlobal,hv] using restore

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  refine ⟨h.originalCode.transport s t inst p.toLayout hf hm ht,h.index569,?_,h.index573,?_,h.growthIndex,?_⟩
  · rw [hf];exact h.function569
  · rw [hf];exact h.function573
  · rw [hf];exact h.growthFunction

theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (paid s op n) inst p := by
  induction n with
  | zero=>exact h
  | succ n ih=>exact ih.transport _ _ inst p rfl rfl rfl
end WNear.Proofs.AllocateRetry
