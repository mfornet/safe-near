import Proofs.StateDispatchStorageState
import Proofs.StateDispatchLengthFrame

/-! Installed-code and memory frames across the actual storage dispatcher. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] checked arguments returned StateDispatchLength.acquired StateDispatchLength.high StateDispatchLength.low StateDispatchPrefix.acquired readI32 writeI32

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
  simpa only [acquired,StateDispatchLength.acquired] using fields_pack s (StateDispatchPrefix.acquired s op p.toLayout) h.1 h.2.1 h.2.2
private theorem fields_low (s : Store NearState) (op : Nat) (p : Layout) : fields (low s op p) = fields s := by
  unfold low StateDispatchLength.low
  rw [fields_store,fields_paid]
  unfold StateDispatchLength.high
  rw [fields_store,fields_paid,fields_acquired]
private theorem fields_nonnull (s : Store NearState) (op : Nat) : fields (ValueReturnOuter.nonnullAfter s op) = fields s := by
  rw [ValueReturnOuter.nonnullAfter,fields_paid,ValueReturnOuter.nonnullEntry,fields_charge,fields_charge]
private theorem fields_checked (s : Store NearState) (op : Nat) (p : Layout) : fields (checked s op p) = fields s := by
  rw [checked,fields_nonnull,fields_paid,fields_paid,fields_low]
private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p) = fields s := by
  rw [arguments,fields_paid,fields_checked]
private theorem of_fields (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : fields t = fields s) : Code t p inst extra := by
  have a : t.funcs = s.funcs := by simpa only [fields] using congrArg (fun x => x.1) hf
  have b : t.modules = s.modules := by simpa only [fields] using congrArg (fun x => x.2.1) hf
  have c : t.tables = s.tables := by simpa only [fields] using congrArg (fun x => x.2.2) hf
  exact h.transport s t p inst extra a b c

theorem Code.checked (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchStorage.checked s op p) p inst extra :=
  of_fields s _ p inst extra h (fields_checked s op p)
theorem Code.arguments (s : Store NearState) (op : Nat) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) : Code (StateDispatchStorage.arguments s op p) p inst extra :=
  of_fields s _ p inst extra h (fields_arguments s op p)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_charge (s : Store NearState) (n : Nat) : (chargedStore s n).mems = s.mems := rfl

theorem checked_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (checked s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  rw [checked,ValueReturnOuter.nonnullAfter,mems_paid,ValueReturnOuter.nonnullEntry,mems_charge,mems_charge,mems_paid,mems_paid]
  exact StateDispatchLength.low_memory s op p hm

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (arguments s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
  rw [arguments,mems_paid]; exact checked_memory s op p hm

theorem returned_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (returned cfg s p ctx key value).mems[p.memoryIndex]? = some (lowMemory p) := by
  unfold returned
  exact StateReadStorage.callAfter_memory cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie
    (keyLen p) (keyPtr p) 0 key value p.memoryIndex (lowMemory p) hi (arguments_memory s cfg.regularOpCost p hm)

private theorem fields_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) : fields (returned cfg s p ctx key value) = fields s := by
  have h := StateReadStorage.callAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie (keyLen p) (keyPtr p) 0 key value
  have a : fields (returned cfg s p ctx key value) = fields (arguments s cfg.regularOpCost p) := by
    simpa only [returned] using fields_pack (arguments s cfg.regularOpCost p)
      (StateReadStorage.callAfter cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie (keyLen p) (keyPtr p) 0 key value) h.1 h.2.1 h.2.2.1
  exact a.trans (fields_arguments s cfg.regularOpCost p)

theorem Code.returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (inst extra : Nat)
    (ctx : NearInterface.Context) (key value : List UInt8)
    (h : Code s p inst extra) : Code (StateDispatchStorage.returned cfg s p ctx key value) p inst extra :=
  of_fields s _ p inst extra h (fields_returned cfg s p ctx key value)

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem globals_store (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    (storeI32 s index address m v).globals = s.globals := rfl
private theorem globals_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).globals = s.globals := rfl
private theorem globals_low (s : Store NearState) (op : Nat) (p : Layout) :
    (low s op p).globals = (acquired s op p).globals := by
  unfold low StateDispatchLength.low
  rw [globals_store,globals_paid]
  unfold StateDispatchLength.high
  rw [globals_store,globals_paid]
private theorem globals_checked (s : Store NearState) (op : Nat) (p : Layout) :
    (checked s op p).globals = (acquired s op p).globals := by
  rw [checked,ValueReturnOuter.nonnullAfter,globals_paid,ValueReturnOuter.nonnullEntry,
    globals_charge,globals_charge,globals_paid,globals_paid,globals_low]
private theorem globals_arguments (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals = (acquired s op p).globals := by
  rw [arguments,globals_paid,globals_checked]
private theorem globals_returned (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (returned cfg s p ctx key value).globals = (arguments s cfg.regularOpCost p).globals := by
  unfold returned
  exact (StateReadStorage.callAfter_fields cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie (keyLen p) (keyPtr p) 0 key value).2.2.2
private theorem global_transport (s t : Store NearState) (index : Nat) (value : GlobalInst)
    (h : t.globals = s.globals) (hg : s.globals[index]? = some value) :
    t.globals[index]? = some value := by rw [h]; exact hg

theorem checked_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (checked s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have h := StateDispatchPrefix.acquired_global s op p.toLayout hg
  have hh : (acquired s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simpa only [acquired,StateDispatchLength.acquired,scratch,StateDispatchLength.scratch] using h
  exact global_transport (acquired s op p) (checked s op p) p.globalIndex
    {p.global with value := .i32 (scratch p)} (globals_checked s op p) hh

theorem returned_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) (hg : s.globals[p.globalIndex]? = some p.global) :
    (returned cfg s p ctx key value).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have ha : (returned cfg s p ctx key value).globals = (checked s cfg.regularOpCost p).globals := by
    rw [globals_returned,globals_arguments,globals_checked]
  exact global_transport (checked s cfg.regularOpCost p) (returned cfg s p ctx key value) p.globalIndex
    {p.global with value := .i32 (scratch p)} ha (checked_global s cfg.regularOpCost p hg)

end WNear.Proofs.StateDispatchStorage
