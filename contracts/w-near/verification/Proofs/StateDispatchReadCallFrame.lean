import Proofs.StateDispatchReadCall

/-! Exact code and global-array frames of the complete actual435 call. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] acquired checked arguments returned finalStore callAfter
  StateDispatchReadBorrow.after StateDispatchReadTail.after StateDispatchReadTail.cleaned StateDispatchReadTail.returned
  StateDispatchReadFinish.after StateDispatchReadFinish.checked

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_charge (s : Store NearState) (cost : Nat) : fields (chargedStore s cost)=fields s := rfl
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s := rfl
private theorem fields_global (s : Store NearState) (i : Nat) (v : Value) : fields (setGlobal s i v)=fields s := rfl
private theorem fields_pack (s t : Store NearState) (h : t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables) :
    fields t=fields s := Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields_acquired (s : Store NearState) (op : Nat) (p : Layout) : fields (acquired s op p)=fields s := by
  unfold acquired
  exact fields_pack s _ (StateDispatchPrefix.acquired_fields s op p.toLayout)
private theorem fields_borrow (s : Store NearState) (op index : Nat) (memory : Memory) (sp : UInt32) :
    fields (StateDispatchReadBorrow.after s op index memory sp)=fields s := by
  simp only [StateDispatchReadBorrow.after,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,
    StateDispatchReadBorrow.low,StateDispatchReadBorrow.high,fields_charge,fields_paid,fields_store]
private theorem fields_checked (s : Store NearState) (op : Nat) (p : Layout) : fields (checked s op p)=fields s := by
  rw [checked,fields_borrow,fields_acquired]
private theorem fields_read (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) :
    fields (StateReadRegister.readCallAfter cfg s mi ptr bytes)=fields s := by
  have h := StateReadRegister.readCallAfter_fields cfg s mi ptr bytes
  exact fields_pack s _ ⟨h.1,h.2.1,h.2.2.1⟩
private theorem fields_clean (s : Store NearState) (op i : Nat) (counter : UInt32) (m : Memory) :
    fields (StateDispatchReadCleanup.after s op i counter m)=fields s := by
  have h := StateDispatchReadCleanup.after_fields s op i counter m
  exact fields_pack s _ ⟨h.1,h.2.1,h.2.2.1⟩
private theorem fields_finish (s : Store NearState) (op i : Nat) (scratch : UInt32) :
    fields (StateDispatchReadFinish.after s op i scratch)=fields s := by
  simp only [StateDispatchReadFinish.after,StateDispatchReadFinish.checked,ValueReturnOuter.checkAfter,
    ValueReturnOuter.nonnullEntry,ValueReturnBorrow.checkedStore,fields_global,fields_paid,fields_charge]

theorem finalStore_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    (finalStore cfg s p bytes).funcs=s.funcs ∧ (finalStore cfg s p bytes).modules=s.modules ∧
    (finalStore cfg s p bytes).tables=s.tables := by
  have eq : fields (finalStore cfg s p bytes)=fields s := by
    rw [finalStore,StateDispatchReadTail.after,fields_finish,StateDispatchReadTail.cleaned,fields_clean,
      StateDispatchReadTail.returned,fields_read,StateDispatchReadTail.arguments,fields_paid,fields_checked]
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    (callAfter cfg s p bytes).funcs=s.funcs ∧ (callAfter cfg s p bytes).modules=s.modules ∧
    (callAfter cfg s p bytes).tables=s.tables := by
  unfold callAfter
  exact finalStore_fields cfg (entered s cfg.regularOpCost) p bytes

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem globals_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).globals=s.globals := rfl
private theorem globals_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : (storeI32 s i a m v).globals=s.globals := rfl
private theorem globals_borrow (s : Store NearState) (op index : Nat) (memory : Memory) (sp : UInt32) :
    (StateDispatchReadBorrow.after s op index memory sp).globals=s.globals := by
  simp only [StateDispatchReadBorrow.after,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,
    StateDispatchReadBorrow.low,StateDispatchReadBorrow.high,globals_charge,globals_paid,globals_store]
private theorem globals_checked (s : Store NearState) (op : Nat) (p : Layout) :
    (checked s op p).globals=(acquired s op p).globals := by
  rw [checked,globals_borrow]
private theorem globals_read (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) :
    (StateReadRegister.readCallAfter cfg s mi ptr bytes).globals=s.globals :=
  (StateReadRegister.readCallAfter_fields cfg s mi ptr bytes).2.2.2
private theorem globals_clean (s : Store NearState) (op i : Nat) (counter : UInt32) (m : Memory) :
    (StateDispatchReadCleanup.after s op i counter m).globals=s.globals :=
  (StateDispatchReadCleanup.after_fields s op i counter m).2.2.2

private theorem globals_cleaned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (StateDispatchReadTail.cleaned cfg (checked s cfg.regularOpCost p) p bytes).globals=
      (StateDispatchPrefix.reserved s cfg.regularOpCost p.toLayout).globals := by
  rw [StateDispatchReadTail.cleaned,globals_clean,StateDispatchReadTail.returned,globals_read,
    StateDispatchReadTail.arguments,globals_paid,globals_checked]
  unfold acquired
  exact StateDispatchPrefix.acquired_globals s cfg.regularOpCost p.toLayout hg

theorem finalStore_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (finalStore cfg s p bytes).globals=s.globals := by
  let clean := StateDispatchReadTail.cleaned cfg (checked s cfg.regularOpCost p) p bytes
  have eq := globals_cleaned cfg s p bytes hg
  have cg : clean.globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
    rw [eq]
    exact StateDispatchPrefix.reserved_global s cfg.regularOpCost p.toLayout hg
  have check := ValueReturnBorrow.checkedStore_globals
    (ValueReturnOuter.nonnullEntry (paid clean cfg.regularOpCost 1) cfg.regularOpCost) cfg.regularOpCost p.globalIndex
    (scratch p) {p.global with value:=.i32 (scratch p)} cg rfl
  have checkedEq : (StateDispatchReadFinish.checked clean cfg.regularOpCost p.globalIndex (scratch p)).globals=clean.globals := by
    simpa only [StateDispatchReadFinish.checked,ValueReturnOuter.checkAfter,ValueReturnOuter.nonnullEntry,
      globals_charge,globals_paid] using check
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  have endSP : scratch p+16=p.sp := UInt32.sub_add_cancel _ _
  unfold finalStore StateDispatchReadTail.after StateDispatchReadFinish.after
  change (setGlobal (paid (StateDispatchReadFinish.checked clean cfg.regularOpCost p.globalIndex (scratch p))
    cfg.regularOpCost 4) p.globalIndex (.i32 (scratch p+16))).globals=s.globals
  simp only [setGlobal,globals_paid]
  rw [checkedEq,eq]
  have prefixEnd : StateDispatchPrefix.scratch p.toLayout+16=p.sp := endSP
  simpa only [StateDispatchPrefix.reserved,setGlobal,globals_paid,hv,scratch,prefixEnd] using restore

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p bytes).globals=s.globals := by
  unfold callAfter
  exact finalStore_globals cfg (entered s cfg.regularOpCost) p bytes hg hv
end WNear.Proofs.StateDispatchRead
