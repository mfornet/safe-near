import Proofs.ValueReturnOuterGlobals
import Proofs.ValueReturnOuterCodeFrame

/-! The complete normal outer cleanup restores the exact incoming global. -/
namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

attribute [local irreducible] ValueReturnBorrowCounters.releasedStore ValueReturnOuter.releaseAfter
  ValueReturnOuter.checkAfter ValueReturnOuter.epilogueAfter ValueReturnOuter.cleanupAfter
  ValueReturnOuter.nonnullEntry ValueReturnBorrow.checkedStore

private theorem charged_globals (s : Store NearState) (cost : Nat) :
    (chargedStore s cost).globals = s.globals := rfl

private theorem resource_globals (s t : Store NearState)
    (h : {t with mems := s.mems, host := s.host} = s) : t.globals = s.globals := by
  have hp := congrArg (fun x : Store NearState => x.globals) h
  exact hp

private theorem release_globals (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (ValueReturnOuter.releaseAfter s op index counter memory).globals = s.globals := by
  have hr := ValueReturnBorrowCounters.releasedStore_resources (ValueReturnOuter.nonnullEntry s op) op index counter memory
  have hp := resource_globals _ _ hr
  rw [ValueReturnOuter.releaseAfter, hp, ValueReturnOuter.nonnullEntry, charged_globals, charged_globals]

private theorem check_globals (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hv : global.value = .i32 sp) :
    (ValueReturnOuter.checkAfter s op index sp).globals = s.globals := by
  have hentry : (ValueReturnOuter.nonnullEntry s op).globals = s.globals := by
    rw [ValueReturnOuter.nonnullEntry, charged_globals, charged_globals]
  have hg' : (ValueReturnOuter.nonnullEntry s op).globals[index]? = some global := by rw [hentry]; exact hg
  have hc := ValueReturnBorrow.checkedStore_globals (ValueReturnOuter.nonnullEntry s op) op index sp global hg' hv
  rw [ValueReturnOuter.checkAfter, hc, hentry]

private theorem epilogue_globals (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hv : global.value = .i32 sp) :
    (ValueReturnOuter.epilogueAfter s op index sp).globals = (setGlobal s index (.i32 (sp + 16))).globals := by
  have hpaid : (paid s op 1).globals[index]? = some global := by rw [paid_globals]; exact hg
  have hc := check_globals (paid s op 1) op index sp global hpaid hv
  simp only [ValueReturnOuter.epilogueAfter, setGlobal, paid_globals, hc]

private theorem cleanup_globals (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp counter : UInt32) (memory : Memory) (global : GlobalInst)
    (hg : s.globals[globalIndex]? = some global) (hv : global.value = .i32 sp) :
    (ValueReturnOuter.cleanupAfter s op globalIndex memoryIndex sp counter memory).globals =
      (setGlobal s globalIndex (.i32 (sp + 16))).globals := by
  let stage := chargedStore (ValueReturnOuter.releaseAfter (paid s op 5) op memoryIndex counter memory) op
  have hs : stage.globals = s.globals := by
    rw [show stage = chargedStore (ValueReturnOuter.releaseAfter (paid s op 5) op memoryIndex counter memory) op from rfl,
      charged_globals, release_globals, paid_globals]
  have hstage : stage.globals[globalIndex]? = some global := by rw [hs]; exact hg
  have he := epilogue_globals stage op globalIndex sp global hstage hv
  have hmodify := congrArg (fun arr => arr.modify globalIndex (fun g => {g with value := .i32 (sp + 16)})) hs
  have hset : (setGlobal stage globalIndex (.i32 (sp + 16))).globals =
      (setGlobal s globalIndex (.i32 (sp + 16))).globals := hmodify
  rw [ValueReturnOuter.cleanupAfter]
  exact he.trans hset

/-- The normal f456 final store restores the original global's type,
mutability and value. It does not need an additional post-store lookup premise. -/
theorem finalStore_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hv : p.global.value = .i32 p.sp) :
    (finalStore cfg s p).globals[p.globalIndex]? = some p.global := by
  have hr := returned_globals cfg s p hg
  have hc := cleanup_globals (returned cfg s p) cfg.regularOpCost p.globalIndex p.memoryIndex
    (scratch p) (counter p) (lowMemory p) {p.global with value := .i32 (scratch p)} hr rfl
  change (ValueReturnOuter.cleanupAfter (returned cfg s p) cfg.regularOpCost p.globalIndex p.memoryIndex
    (scratch p) (counter p) (lowMemory p)).globals[p.globalIndex]? = some p.global
  rw [hc]
  have he : ({p.global with value := .i32 (scratch p + 16)} : GlobalInst) = p.global := by
    have hcancel : scratch p + 16 = p.sp := UInt32.sub_add_cancel p.sp 16
    rw [hcancel, ← hv]
  simp [setGlobal, Array.getElem?_modify, hr, he]

private def codeFields (s : Store NearState) := (s.funcs, s.modules, s.tables)

private theorem fields_paid (s : Store NearState) (op n : Nat) :
    codeFields (paid s op n) = codeFields s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem fields_charge (s : Store NearState) (cost : Nat) :
    codeFields (chargedStore s cost) = codeFields s := rfl

private theorem fields_global (s : Store NearState) (index : Nat) (value : Value) :
    codeFields (setGlobal s index value) = codeFields s := rfl

private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    codeFields (storeI32 s index address memory value) = codeFields s := rfl

attribute [local irreducible] codeFields

private theorem cleanup_fields (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp counter : UInt32) (memory : Memory) :
    codeFields (ValueReturnOuter.cleanupAfter s op globalIndex memoryIndex sp counter memory) = codeFields s := by
  simp only [ValueReturnOuter.cleanupAfter, ValueReturnOuter.epilogueAfter, ValueReturnOuter.releaseAfter,
    ValueReturnOuter.checkAfter, ValueReturnOuter.nonnullEntry, ValueReturnBorrow.checkedStore,
    ValueReturnBorrowCounters.releasedStore, ValueReturnBorrowCounters.calledSwapStore,
    ValueReturnBorrowCounters.swapStore, ValueReturnBorrowCounters.swapEntryStore,
    fields_paid, fields_charge, fields_global, fields_store]

/-- The final counter cleanup and shadow-stack restoration preserve every
function, module and table fact in the original code certificate. -/
theorem finalStore_code (cfg : WasmConfig) (s : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (finalStore cfg s p) p inst extra := by
  have hr := Code.returned cfg s p inst extra h
  have hf := cleanup_fields (returned cfg s p) cfg.regularOpCost p.globalIndex p.memoryIndex
    (scratch p) (counter p) (lowMemory p)
  have hfuncs : (finalStore cfg s p).funcs = (returned cfg s p).funcs := by
    simpa only [codeFields, finalStore] using congrArg (fun x => x.1) hf
  have hmodules : (finalStore cfg s p).modules = (returned cfg s p).modules := by
    simpa only [codeFields, finalStore] using congrArg (fun x => x.2.1) hf
  have htables : (finalStore cfg s p).tables = (returned cfg s p).tables := by
    simpa only [codeFields, finalStore] using congrArg (fun x => x.2.2) hf
  exact hr.transport _ _ p inst extra hfuncs hmodules htables

end WNear.Proofs.ValueReturnOuterBody
