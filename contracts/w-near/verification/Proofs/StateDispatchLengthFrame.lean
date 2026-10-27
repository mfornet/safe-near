import Proofs.StateDispatchLengthState
import Proofs.StateDispatchPrefixFrame
import Proofs.StateReadRegisterFrame

/-! Resource frames between the actual phases of the register-length dispatcher. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] acquired high low checked arguments returned cleaned finalStore StateDispatchPrefix.acquired readI32 writeI32

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (n : Nat) : fields (chargedStore s n) = fields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    fields (storeI32 s index address m v) = fields s := rfl
private theorem fields_pack (s t : Store NearState) (hf : t.funcs = s.funcs)
    (hm : t.modules = s.modules) (ht : t.tables = s.tables) : fields t = fields s :=
  Prod.ext hf (Prod.ext hm ht)
private theorem fields_acquired (s : Store NearState) (op : Nat) (p : Layout) : fields (acquired s op p) = fields s := by
  have h := StateDispatchPrefix.acquired_fields s op p.toLayout
  simpa only [acquired] using fields_pack s (StateDispatchPrefix.acquired s op p.toLayout) h.1 h.2.1 h.2.2
private theorem fields_high (s : Store NearState) (op : Nat) (p : Layout) : fields (high s op p) = fields s := by
  unfold high
  rw [fields_store,fields_paid,fields_acquired]
private theorem fields_low (s : Store NearState) (op : Nat) (p : Layout) : fields (low s op p) = fields s := by
  unfold low
  rw [fields_store,fields_paid,fields_high]
private theorem fields_nonnull (s : Store NearState) (op : Nat) : fields (ValueReturnOuter.nonnullAfter s op) = fields s := by
  rw [ValueReturnOuter.nonnullAfter,fields_paid,ValueReturnOuter.nonnullEntry,fields_charge,fields_charge]
private theorem fields_checked (s : Store NearState) (op : Nat) (p : Layout) : fields (checked s op p) = fields s := by
  unfold checked
  rw [fields_nonnull,fields_paid,fields_low]
private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p) = fields s := by
  rw [arguments,fields_paid,fields_checked]
private theorem of_fields (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : fields t = fields s) : Code t p inst extra := by
  have a : t.funcs = s.funcs := by simpa only [fields] using congrArg (fun x => x.1) hf
  have b : t.modules = s.modules := by simpa only [fields] using congrArg (fun x => x.2.1) hf
  have c : t.tables = s.tables := by simpa only [fields] using congrArg (fun x => x.2.2) hf
  exact h.transport s t p inst extra a b c

theorem Code.checked (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchLength.checked s op p) p inst extra :=
  of_fields s _ p inst extra h (fields_checked s op p)
theorem Code.arguments (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchLength.arguments s op p) p inst extra :=
  of_fields s _ p inst extra h (fields_arguments s op p)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_charge (s : Store NearState) (n : Nat) : (chargedStore s n).mems = s.mems := rfl

theorem high_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (high s op p).mems[p.memoryIndex]? = some (highMemory p) := by
  unfold high highMemory
  apply storeI32_memory
  simpa only [acquired, acquiredMemory, StateDispatchPrefix.acquiredMemory, scratch, paid, chargedStore] using StateDispatchPrefix.acquired_memory s op p.toLayout hm

theorem low_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (low s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  have hh : (paid (high s op p) op 5).mems[p.memoryIndex]? = some (highMemory p) := by
    rw [mems_paid]
    exact high_memory s op p hm
  unfold low lowMemory
  exact storeI32_memory (paid (high s op p) op 5) p.memoryIndex ((scratch p).toNat + 8) (highMemory p) (borrowed p) hh

theorem checked_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (checked s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  unfold checked
  rw [ValueReturnOuter.nonnullAfter,mems_paid,ValueReturnOuter.nonnullEntry,mems_charge,mems_charge,mems_paid]
  exact low_memory s op p hm

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  unfold arguments
  rw [mems_paid]
  exact checked_memory s op p hm

theorem returned_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (returned cfg s p).mems[p.memoryIndex]? = some (lowMemory p) := by
  unfold returned
  exact StateReadRegister.lengthCallAfter_memory cfg (arguments s cfg.regularOpCost p) p.mi p.memoryIndex (lowMemory p) hi (arguments_memory s cfg.regularOpCost p hm)

private theorem fields_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) : fields (returned cfg s p) = fields s := by
  have h := StateReadRegister.lengthCallAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi
  have a : fields (returned cfg s p) = fields (arguments s cfg.regularOpCost p) := by
    simpa only [returned] using fields_pack (arguments s cfg.regularOpCost p)
      (StateReadRegister.lengthCallAfter cfg (arguments s cfg.regularOpCost p) p.mi) h.1 h.2.1 h.2.2.1
  exact a.trans (fields_arguments s cfg.regularOpCost p)
private theorem fields_release (s : Store NearState) (op index : Nat) (counter : UInt32) (m : Memory) :
    fields (StateDispatchLengthCleanup.after s op index counter m) = fields s := by
  simp only [StateDispatchLengthCleanup.after,StateDispatchLengthCleanup.released,StateDispatchLengthCleanup.releaseBefore,
    ValueReturnOuter.releaseAfter,ValueReturnOuter.nonnullEntry,ValueReturnBorrowCounters.releasedStore,
    ValueReturnBorrowCounters.calledSwapStore,ValueReturnBorrowCounters.swapStore,ValueReturnBorrowCounters.swapEntryStore,
    fields_paid,fields_charge,fields_store]
theorem Code.returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchLength.returned cfg s p) p inst extra :=
  of_fields s _ p inst extra h (fields_returned cfg s p)
theorem Code.cleaned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchLength.cleaned cfg s p) p inst extra := by
  apply of_fields s _ p inst extra h
  rw [StateDispatchLength.cleaned,fields_release,fields_returned]

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem globals_charge (s : Store NearState) (op : Nat) : (chargedStore s op).globals = s.globals := rfl
private theorem globals_store (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    (storeI32 s index address m v).globals = s.globals := rfl
private theorem globals_checked (s : Store NearState) (op : Nat) (p : Layout) :
    (checked s op p).globals = (acquired s op p).globals := by
  unfold checked
  rw [ValueReturnOuter.nonnullAfter,globals_paid,ValueReturnOuter.nonnullEntry]
  rw [globals_charge,globals_charge,globals_paid,low,globals_store,globals_paid,high,globals_store,globals_paid]
private theorem globals_arguments (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals = (acquired s op p).globals := by
  rw [arguments,globals_paid,globals_checked]
private theorem globals_release (s : Store NearState) (op index : Nat) (counter : UInt32) (m : Memory) :
    (StateDispatchLengthCleanup.after s op index counter m).globals = s.globals := by
  simp only [StateDispatchLengthCleanup.after,StateDispatchLengthCleanup.released,StateDispatchLengthCleanup.releaseBefore,
    ValueReturnOuter.releaseAfter,ValueReturnOuter.nonnullEntry,ValueReturnBorrowCounters.releasedStore,
    ValueReturnBorrowCounters.calledSwapStore,ValueReturnBorrowCounters.swapStore,ValueReturnBorrowCounters.swapEntryStore,
    globals_paid,chargedStore,globals_store]
private theorem globals_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (returned cfg s p).globals = (arguments s cfg.regularOpCost p).globals := by
  unfold returned
  exact (StateReadRegister.lengthCallAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi).2.2.2

theorem cleaned_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (cleaned cfg s p).globals = (acquired s cfg.regularOpCost p).globals := by
  rw [cleaned,globals_release,globals_returned,globals_arguments]

private theorem global_transport (s t : Store NearState) (index : Nat) (value : GlobalInst)
    (h : t.globals = s.globals) (hg : s.globals[index]? = some value) :
    t.globals[index]? = some value := by rw [h]; exact hg

theorem checked_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (checked s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have hh : (acquired s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simpa only [acquired,scratch] using StateDispatchPrefix.acquired_global s op p.toLayout hg
  exact global_transport (acquired s op p) (checked s op p) p.globalIndex
    {p.global with value := .i32 (scratch p)} (globals_checked s op p) hh

theorem cleaned_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (cleaned cfg s p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have h := StateDispatchPrefix.acquired_global s cfg.regularOpCost p.toLayout hg
  have hh : (acquired s cfg.regularOpCost p).globals[p.globalIndex]? =
      some {p.global with value := .i32 (scratch p)} := by
    simpa only [acquired,scratch] using h
  exact global_transport (acquired s cfg.regularOpCost p) (cleaned cfg s p) p.globalIndex
    {p.global with value := .i32 (scratch p)} (cleaned_globals cfg s p) hh

end WNear.Proofs.StateDispatchLength
