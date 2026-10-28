import Proofs.StateReadStorageOuterMemory

/-! Exact code arrays and restored guest globals of the complete actual f459 call. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] StateDispatchLength.acquired StateDispatchLength.high StateDispatchLength.low checked arguments returned finalStore callAfter

private def cleaned (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :=
  StateDispatchStorageCleanup.after (returned cfg s p ctx key value) cfg.regularOpCost p.memoryIndex (counter p) (lowMemory p)

private theorem finalStore_eq (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    finalStore cfg s p ctx key value=StateDispatchStorageFinish.after (cleaned cfg s p ctx key value)
      cfg.regularOpCost p.globalIndex (scratch p) := by
  unfold finalStore StateDispatchStorageTail.after StateDispatchStorageTail.cleaned
    StateDispatchStorageTail.returned StateDispatchStorageTail.arguments cleaned returned arguments
  rfl

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (n : Nat) : fields (chargedStore s n) = fields s := rfl
private theorem fields_global (s : Store NearState) (index : Nat) (v : Value) : fields (setGlobal s index v) = fields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) : fields (storeI32 s index address memory v) = fields s := rfl
private theorem fields_pack (s t : Store NearState) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    fields t = fields s := Prod.ext hf (Prod.ext hm ht)
private theorem fields_project (s t : Store NearState) (h : fields t = fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
private theorem fields_acquired (s : Store NearState) (op : Nat) (p : Layout) : fields (acquired s op p)=fields s := by
  have h := StateDispatchPrefix.acquired_fields s op p.toLayout
  simpa only [acquired,StateDispatchLength.acquired] using fields_pack s (StateDispatchPrefix.acquired s op p.toLayout) h.1 h.2.1 h.2.2
private theorem fields_high (s : Store NearState) (op : Nat) (p : Layout) : fields (high s op p)=fields s := by
  unfold high StateDispatchLength.high
  rw [fields_store,fields_paid,fields_acquired]
private theorem fields_low (s : Store NearState) (op : Nat) (p : Layout) : fields (low s op p)=fields s := by
  unfold low StateDispatchLength.low
  rw [fields_store,fields_paid,fields_high]
private theorem fields_checked (s : Store NearState) (op : Nat) (p : Layout) : fields (checked s op p)=fields s := by
  unfold checked
  rw [ValueReturnOuter.nonnullAfter,fields_paid,ValueReturnOuter.nonnullEntry,fields_charge,fields_charge,fields_paid,fields_paid,fields_low]
private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p)=fields s := by
  rw [arguments,fields_paid,fields_checked]
private theorem fields_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) : fields (returned cfg s p ctx key value)=fields s := by
  have h := StateReadStorage.callAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie (keyLen p) (keyPtr p) 0 key value
  have he := fields_pack (arguments s cfg.regularOpCost p) _ h.1 h.2.1 h.2.2.1
  unfold returned
  exact he.trans (fields_arguments s cfg.regularOpCost p)
private theorem fields_cleanup (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    fields (StateDispatchStorageCleanup.after s op index counter memory)=fields s := by
  have h := StateDispatchStorageCleanup.after_fields s op index counter memory
  exact fields_pack s _ h.1 h.2.1 h.2.2.1
private theorem fields_finish (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    fields (StateDispatchStorageFinish.after s op index scratch)=fields s := by
  have h := StateDispatchReturn.callAfter_fields (paid s op 2) op index scratch
  have he := fields_pack (paid s op 2) _ h.2.1 h.2.2.1 h.2.2.2
  unfold StateDispatchStorageFinish.after StateDispatchStorageFinish.afterReturn StateDispatchLengthFinish.afterReturn
  rw [fields_paid,fields_global,fields_paid,fields_paid]
  unfold StateDispatchStorageFinish.returned
  exact he.trans (fields_paid s op 2)

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) :
    (callAfter cfg s p ctx key value).funcs=s.funcs ∧ (callAfter cfg s p ctx key value).modules=s.modules ∧ (callAfter cfg s p ctx key value).tables=s.tables := by
  have h : fields (callAfter cfg s p ctx key value)=fields s := by
    rw [callAfter]
    rw [finalStore_eq]
    rw [fields_finish,cleaned,fields_cleanup,fields_returned,entered,fields_charge,fields_charge]
  exact fields_project s _ h

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem finish_globals (s : Store NearState) (op index : Nat) (scratch : UInt32)
    (global : GlobalInst) (hg : s.globals[index]?=some global) (hv : global.value=.i32 scratch) :
    (StateDispatchStorageFinish.after s op index scratch).globals =
      (setGlobal s index (.i32 (scratch+16))).globals := by
  have h : (StateDispatchStorageFinish.returned s op index scratch).globals=s.globals :=
    StateDispatchReturn.callAfter_globals (paid s op 2) op index scratch global hg hv
  simp only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.afterReturn,StateDispatchLengthFinish.afterReturn,globals_paid,setGlobal]
  rw [h]

private theorem restore_globals (s t : Store NearState) (index : Nat) (scratch : UInt32) (global : GlobalInst)
    (h : t.globals=(setGlobal s index (.i32 scratch)).globals)
    (hg : s.globals[index]?=some global) :
    (setGlobal t index global.value).globals=s.globals := by
  have restore := StorePairCaller.setGlobal_restore s index (.i32 scratch) global hg
  simp only [setGlobal] at h ⊢
  rw [h]
  exact restore

private theorem globals_charge (s : Store NearState) (op : Nat) : (chargedStore s op).globals=s.globals := rfl
private theorem globals_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : (storeI32 s i a m v).globals=s.globals := rfl
private theorem globals_arguments (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals=(acquired s op p).globals := by
  rw [arguments,globals_paid,checked,ValueReturnOuter.nonnullAfter,globals_paid,
    ValueReturnOuter.nonnullEntry,globals_charge,globals_charge,globals_paid,globals_paid]
  unfold low StateDispatchLength.low
  rw [globals_store,globals_paid]
  unfold StateDispatchLength.high
  rw [globals_store,globals_paid]
private theorem globals_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (returned cfg s p ctx key value).globals=(arguments s cfg.regularOpCost p).globals :=
  by
  unfold returned
  exact (StateReadStorage.callAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie (keyLen p) (keyPtr p) 0 key value).2.2.2
private theorem globals_cleanup (s : Store NearState) (op i : Nat) (counter : UInt32) (m : Memory) :
    (StateDispatchStorageCleanup.after s op i counter m).globals=s.globals :=
  (StateDispatchStorageCleanup.after_fields s op i counter m).2.2.2

theorem finalStore_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (finalStore cfg s p ctx key value).globals=s.globals := by
  have hclean : (cleaned cfg s p ctx key value).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
    rw [cleaned,globals_cleanup,globals_returned,globals_arguments,acquired,StateDispatchLength.acquired]
    rw [StateDispatchPrefix.acquired_globals s cfg.regularOpCost p.toLayout hg]
    simp only [StateDispatchPrefix.reserved,setGlobal,globals_paid,scratch,StateDispatchLength.scratch]
  have hf := finish_globals (cleaned cfg s p ctx key value) cfg.regularOpCost p.globalIndex (scratch p)
    {p.global with value:=.i32 (scratch p)} (by rw [hclean];simp only [setGlobal,Array.getElem?_modify,hg,Option.map_some];rfl) rfl
  have restored := restore_globals s (cleaned cfg s p ctx key value) p.globalIndex (scratch p) p.global hclean hg
  have pointer : scratch p+16=p.sp := by simp only [scratch,StateDispatchLength.scratch,StateDispatchPrefix.scratch,UInt32.sub_add_cancel]
  rw [finalStore_eq]
  rw [hf,pointer]
  simpa only [hv] using restored

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p ctx key value).globals=s.globals := by
  unfold callAfter
  exact finalStore_globals cfg (entered s cfg.regularOpCost) p ctx key value hg hv

end WNear.Proofs.StateDispatchStorage
