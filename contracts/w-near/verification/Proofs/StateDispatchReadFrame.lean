import Proofs.StateDispatchReadState
import Proofs.StateDispatchPrefixFrame
import Proofs.StateDispatchPrefixHost
import Proofs.StateReadRegisterFrame

/-! Code, memory and host frames of the actual register-copy dispatcher. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] acquired checked arguments returned StateDispatchPrefix.acquired readI32 writeI32

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (n : Nat) : fields (chargedStore s n) = fields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    fields (storeI32 s index address m v) = fields s := rfl
private theorem fields_pack (s t : Store NearState) (hf : t.funcs = s.funcs)
    (hm : t.modules = s.modules) (ht : t.tables = s.tables) : fields t = fields s := Prod.ext hf (Prod.ext hm ht)
private theorem fields_acquired (s : Store NearState) (op : Nat) (p : Layout) : fields (acquired s op p) = fields s := by
  have h := StateDispatchPrefix.acquired_fields s op p.toLayout
  simpa only [acquired] using fields_pack s (StateDispatchPrefix.acquired s op p.toLayout) h.1 h.2.1 h.2.2
private theorem fields_borrow (s : Store NearState) (op index : Nat) (m : Memory) (sp : UInt32) :
    fields (StateDispatchReadBorrow.after s op index m sp) = fields s := by
  simp only [StateDispatchReadBorrow.after,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,
    StateDispatchReadBorrow.low,StateDispatchReadBorrow.high,fields_paid,fields_charge,fields_store]
private theorem fields_checked (s : Store NearState) (op : Nat) (p : Layout) : fields (checked s op p) = fields s := by
  rw [checked,fields_borrow,fields_acquired]
private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p) = fields s := by
  rw [arguments,fields_paid,fields_checked]
private theorem of_fields (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : fields t = fields s) : Code t p inst extra := by
  have a : t.funcs = s.funcs := by simpa only [fields] using congrArg (fun x => x.1) hf
  have b : t.modules = s.modules := by simpa only [fields] using congrArg (fun x => x.2.1) hf
  have c : t.tables = s.tables := by simpa only [fields] using congrArg (fun x => x.2.2) hf
  exact h.transport s t p inst extra a b c

theorem Code.checked (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchRead.checked s op p) p inst extra :=
  of_fields s _ p inst extra h (fields_checked s op p)
theorem Code.arguments (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchRead.arguments s op p) p inst extra :=
  of_fields s _ p inst extra h (fields_arguments s op p)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_charge (s : Store NearState) (n : Nat) : (chargedStore s n).mems = s.mems := rfl
private theorem borrow_memory (s : Store NearState) (op index : Nat) (m : Memory) (sp : UInt32)
    (hm : s.mems[index]? = some m) :
    (StateDispatchReadBorrow.after s op index m sp).mems[index]? = some (StateDispatchReadBorrow.lowMemory m sp) := by
  have mh : (StateDispatchReadBorrow.high s op index m sp).mems[index]? = some (StateDispatchReadBorrow.highMemory m sp) := by
    unfold StateDispatchReadBorrow.high StateDispatchReadBorrow.highMemory
    apply storeI32_memory
    rw [mems_paid]; exact hm
  have ml : (StateDispatchReadBorrow.low s op index m sp).mems[index]? = some (StateDispatchReadBorrow.lowMemory m sp) := by
    unfold StateDispatchReadBorrow.low StateDispatchReadBorrow.lowMemory
    apply storeI32_memory
    rw [mems_paid]; exact mh
  rw [StateDispatchReadBorrow.after,ValueReturnOuter.nonnullAfter,mems_paid,ValueReturnOuter.nonnullEntry,
    mems_charge,mems_charge,mems_paid,mems_paid]
  exact ml

theorem acquired_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
  simpa only [acquired,acquiredMemory,StateDispatchLength.acquiredMemory,asLength,
    StateDispatchPrefix.acquiredMemory,StateDispatchLength.scratch,StateDispatchPrefix.scratch] using
    StateDispatchPrefix.acquired_memory s op p.toLayout hm

theorem checked_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (checked s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  unfold checked lowMemory
  exact borrow_memory (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p) (acquired_memory s op p hm)

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  rw [arguments,mems_paid]; exact checked_memory s op p hm

theorem returned_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (returned cfg s p bytes).mems[p.memoryIndex]? = some (readMemory p bytes) := by
  unfold returned readMemory
  exact StateReadRegister.readCallAfter_memory cfg (arguments s cfg.regularOpCost p) p.mi p.memoryIndex (lowMemory p)
    (ptr p) bytes hi (arguments_memory s cfg.regularOpCost p hm)

private theorem fields_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    fields (returned cfg s p bytes) = fields s := by
  have h := StateReadRegister.readCallAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi (ptr p) bytes
  have a : fields (returned cfg s p bytes) = fields (arguments s cfg.regularOpCost p) := by
    simpa only [returned] using fields_pack (arguments s cfg.regularOpCost p)
      (StateReadRegister.readCallAfter cfg (arguments s cfg.regularOpCost p) p.mi (ptr p) bytes) h.1 h.2.1 h.2.2.1
  exact a.trans (fields_arguments s cfg.regularOpCost p)

theorem Code.returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (inst extra : Nat) (bytes : List UInt8)
    (h : Code s p inst extra) : Code (StateDispatchRead.returned cfg s p bytes) p inst extra :=
  of_fields s _ p inst extra h (fields_returned cfg s p bytes)

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem globals_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).globals = s.globals := rfl
private theorem globals_store (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    (storeI32 s index address m v).globals = s.globals := rfl
private theorem globals_borrow (s : Store NearState) (op index : Nat) (m : Memory) (sp : UInt32) :
    (StateDispatchReadBorrow.after s op index m sp).globals = s.globals := by
  simp only [StateDispatchReadBorrow.after,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,
    StateDispatchReadBorrow.low,StateDispatchReadBorrow.high,globals_paid,globals_charge,globals_store]
private theorem globals_checked (s : Store NearState) (op : Nat) (p : Layout) :
    (checked s op p).globals = (acquired s op p).globals := by rw [checked,globals_borrow]
private theorem globals_arguments (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals = (acquired s op p).globals := by rw [arguments,globals_paid,globals_checked]
private theorem globals_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    (returned cfg s p bytes).globals = (arguments s cfg.regularOpCost p).globals := by
  unfold returned
  exact (StateReadRegister.readCallAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi (ptr p) bytes).2.2.2
private theorem global_transport (s t : Store NearState) (index : Nat) (value : GlobalInst)
    (h : t.globals = s.globals) (hg : s.globals[index]? = some value) : t.globals[index]? = some value := by rw [h]; exact hg

theorem checked_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (checked s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have hh : (acquired s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simpa only [acquired,scratch] using StateDispatchPrefix.acquired_global s op p.toLayout hg
  exact global_transport (acquired s op p) (checked s op p) p.globalIndex
    {p.global with value := .i32 (scratch p)} (globals_checked s op p) hh

theorem returned_global (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (returned cfg s p bytes).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have ha : (returned cfg s p bytes).globals = (checked s cfg.regularOpCost p).globals := by
    rw [globals_returned,globals_arguments,globals_checked]
  exact global_transport (checked s cfg.regularOpCost p) (returned cfg s p bytes) p.globalIndex
    {p.global with value := .i32 (scratch p)} ha (checked_global s cfg.regularOpCost p hg)

end WNear.Proofs.StateDispatchRead
