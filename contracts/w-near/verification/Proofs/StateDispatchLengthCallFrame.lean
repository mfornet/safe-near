import Proofs.StateDispatchLengthCall
import Proofs.StateDispatchLengthFrame
import Proofs.StateDispatchLengthMemory

/-! Exact code, post-release memory and guest global restoration of actual f440. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] acquired high low checked arguments returned cleaned finalStore
  StateDispatchPrefix.acquired readI32 writeI32

/-- The register-length host preserves memory; the subsequent real release decrements this counter. -/
def finalMemory (p : Layout) := writeI32 (lowMemory p) (counter p).toNat
  (readI32 (lowMemory p) (counter p).toNat+4294967295)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_charge (s : Store NearState) (n : Nat) : (chargedStore s n).mems = s.mems := rfl
private theorem mems_global (s : Store NearState) (index : Nat) (v : Value) : (setGlobal s index v).mems = s.mems := rfl
private theorem cleanup_memory (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (StateDispatchLengthCleanup.after s op index counter memory).mems[index]? =
      some (writeI32 memory counter.toNat (readI32 memory counter.toNat+4294967295)) := by
  unfold StateDispatchLengthCleanup.after StateDispatchLengthCleanup.released ValueReturnOuter.releaseAfter
  rw [mems_paid]
  apply ValueReturnBorrowCounters.releasedStore_memory
  rw [ValueReturnOuter.nonnullEntry,mems_charge,mems_charge,StateDispatchLengthCleanup.releaseBefore,mems_paid]
  exact hm
private theorem finish_mems (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    (StateDispatchLengthFinish.after s op index scratch).mems = s.mems := by
  unfold StateDispatchLengthFinish.after StateDispatchLengthFinish.afterReturn
  rw [mems_paid,mems_global,mems_paid,mems_paid]
  unfold StateDispatchLengthFinish.returned
  rw [(StateDispatchReturn.callAfter_fields (paid s op 2) op index scratch).1,mems_paid]

theorem finalStore_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (finalStore cfg s p).mems[p.memoryIndex]? = some (finalMemory p) := by
  unfold finalStore
  rw [finish_mems]
  unfold cleaned
  exact cleanup_memory (returned cfg s p) cfg.regularOpCost p.memoryIndex (counter p) (lowMemory p)
    (returned_memory cfg s p hi hm)

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (callAfter cfg s p).mems[p.memoryIndex]? = some (finalMemory p) :=
  finalStore_memory cfg (entered s cfg.regularOpCost) p hi hm

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
  simpa only [acquired] using fields_pack s (StateDispatchPrefix.acquired s op p.toLayout) h.1 h.2.1 h.2.2
private theorem fields_high (s : Store NearState) (op : Nat) (p : Layout) : fields (high s op p)=fields s := by
  unfold high
  rw [fields_store,fields_paid,fields_acquired]
private theorem fields_low (s : Store NearState) (op : Nat) (p : Layout) : fields (low s op p)=fields s := by
  unfold low
  rw [fields_store,fields_paid,fields_high]
private theorem fields_checked (s : Store NearState) (op : Nat) (p : Layout) : fields (checked s op p)=fields s := by
  unfold checked
  rw [ValueReturnOuter.nonnullAfter,fields_paid,ValueReturnOuter.nonnullEntry,fields_charge,fields_charge,fields_paid,fields_low]
private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p)=fields s := by
  rw [arguments,fields_paid,fields_checked]
private theorem fields_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (returned cfg s p)=fields s := by
  have h := StateReadRegister.lengthCallAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi
  have he := fields_pack (arguments s cfg.regularOpCost p) _ h.1 h.2.1 h.2.2.1
  unfold returned
  exact he.trans (fields_arguments s cfg.regularOpCost p)
private theorem fields_cleanup (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    fields (StateDispatchLengthCleanup.after s op index counter memory)=fields s := by
  have h := StateDispatchLengthTail.cleanup_fields s op index counter memory
  exact fields_pack s _ h.1 h.2.1 h.2.2.1
private theorem fields_finish (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    fields (StateDispatchLengthFinish.after s op index scratch)=fields s := by
  have h := StateDispatchReturn.callAfter_fields (paid s op 2) op index scratch
  have he := fields_pack (paid s op 2) _ h.2.1 h.2.2.1 h.2.2.2
  unfold StateDispatchLengthFinish.after StateDispatchLengthFinish.afterReturn
  rw [fields_paid,fields_global,fields_paid,fields_paid]
  unfold StateDispatchLengthFinish.returned
  exact he.trans (fields_paid s op 2)

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables := by
  have h : fields (callAfter cfg s p)=fields s := by
    rw [callAfter,finalStore,fields_finish,cleaned,fields_cleanup,fields_returned,entered,fields_charge,fields_charge]
  exact fields_project s _ h

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem finish_globals (s : Store NearState) (op index : Nat) (scratch : UInt32)
    (global : GlobalInst) (hg : s.globals[index]?=some global) (hv : global.value=.i32 scratch) :
    (StateDispatchLengthFinish.after s op index scratch).globals =
      (setGlobal s index (.i32 (scratch+16))).globals := by
  have h : (StateDispatchLengthFinish.returned s op index scratch).globals=s.globals :=
    StateDispatchReturn.callAfter_globals (paid s op 2) op index scratch global hg hv
  simp only [StateDispatchLengthFinish.after,StateDispatchLengthFinish.afterReturn,globals_paid,setGlobal]
  rw [h]

private theorem restore_globals (s t : Store NearState) (index : Nat) (scratch : UInt32) (global : GlobalInst)
    (h : t.globals=(setGlobal s index (.i32 scratch)).globals)
    (hg : s.globals[index]?=some global) :
    (setGlobal t index global.value).globals=s.globals := by
  have restore := StorePairCaller.setGlobal_restore s index (.i32 scratch) global hg
  simp only [setGlobal] at h ⊢
  rw [h]
  exact restore

theorem finalStore_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (finalStore cfg s p).globals=s.globals := by
  have hclean : (cleaned cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
    rw [cleaned_globals,acquired]
    rw [StateDispatchPrefix.acquired_globals s cfg.regularOpCost p.toLayout hg]
    simp only [StateDispatchPrefix.reserved,setGlobal,globals_paid,scratch]
  have hf := finish_globals (cleaned cfg s p) cfg.regularOpCost p.globalIndex (scratch p)
    {p.global with value:=.i32 (scratch p)} (cleaned_global cfg s p hg) rfl
  have restored := restore_globals s (cleaned cfg s p) p.globalIndex (scratch p) p.global hclean hg
  have pointer : scratch p+16=p.sp := by simp only [scratch,StateDispatchPrefix.scratch,UInt32.sub_add_cancel]
  unfold finalStore
  rw [hf,pointer]
  simpa only [hv] using restored

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p).globals=s.globals :=
  finalStore_globals cfg (entered s cfg.regularOpCost) p hg hv

theorem Ready.finalMemory_specs (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (hr : Ready s limits frame callers p extra) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧ (finalMemory p).max=p.memory.max := by
  have low := hr.lowMemory_specs s limits frame callers p extra
  have written := writeI32_spec (lowMemory p) (counter p).toNat
    (readI32 (lowMemory p) (counter p).toNat+4294967295) low.1 hr.counterBound
  exact ⟨written.1,written.2.1.trans low.2.1,written.2.2.1.trans low.2.2⟩

end WNear.Proofs.StateDispatchLength
