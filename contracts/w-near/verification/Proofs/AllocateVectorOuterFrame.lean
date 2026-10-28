import Proofs.AllocateVectorOuterPhases
import Proofs.AllocateVectorFrame

/-! Actual687 array and stack-global frames through the real686 callee. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] reserved guarded arguments allocated after vectorEntered tailAfter exitAfter outputAfter

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (arguments s op p).mems[p.memoryIndex]?=some p.memory := by
  rw [arguments,mems_paid,guarded,mems_paid,reserved,setGlobal,mems_paid]
  exact hm

theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global687) :
    (arguments s op p).globals[p.globalIndex]?=some p.outerGlobal := by
  rw [arguments,globals_paid,guarded,globals_paid,reserved]
  simp only [setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some]
  rw [hn.outerGlobal]
  simp only [ite_true]

theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocated cfg s p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
  unfold allocated allocatedMemory
  apply AllocateVector.after_memory
  unfold vectorEntered
  exact arguments_memory s cfg.regularOpCost p hm

theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global687) :
    (allocated cfg s p).globals=(arguments s cfg.regularOpCost p).globals := by
  have hv : p.outerGlobal.value=.i32 p.outerSP := by rw [hn.outerGlobal]
  have enteredGlobal : (vectorEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost).globals[p.globalIndex]?=some p.outerGlobal := by
    unfold vectorEntered
    exact arguments_global s cfg.regularOpCost p hn hg
  have eq := AllocateVector.after_globals cfg (vectorEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost)
    p.toVector (hn.vector p) enteredGlobal hv
  simpa only [allocated,vectorEntered,chargedStore] using eq

theorem allocated_global (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global687) :
    (allocated cfg s p).globals[p.globalIndex]?=some p.outerGlobal := by
  rw [allocated_globals cfg s p hn hg]
  exact arguments_global s cfg.regularOpCost p hn hg

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_global (s : Store NearState) (i : Nat) (v : Value) : fields (setGlobal s i v)=fields s := rfl
private theorem fields_pack (s t : Store NearState)
    (h : t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables) : fields t=fields s :=
  Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem arguments_fields_eq (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p)=fields s := by
  rw [arguments,fields_paid,guarded,fields_paid,reserved,fields_global,fields_paid]

theorem arguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).funcs=s.funcs ∧ (arguments s op p).modules=s.modules ∧ (arguments s op p).tables=s.tables := by
  have eq := arguments_fields_eq s op p
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩

theorem arguments_code (s : Store NearState) (op inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (arguments s op p) inst p := by
  have fields := arguments_fields s op p
  exact h.transport s _ inst p fields.1 fields.2.1 fields.2.2

theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).funcs=s.funcs ∧ (allocated cfg s p).modules=s.modules ∧ (allocated cfg s p).tables=s.tables := by
  have body := AllocateVector.after_fields cfg (vectorEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost) p.toVector
  have eq := fields_pack _ _ body
  have all : fields (allocated cfg s p)=fields s := by
    unfold allocated
    rw [eq]
    unfold vectorEntered
    change fields (arguments s cfg.regularOpCost p)=fields s
    exact arguments_fields_eq s cfg.regularOpCost p
  exact ⟨congrArg (fun x=>x.1) all,congrArg (fun x=>x.2.1) all,congrArg (fun x=>x.2.2) all⟩

theorem allocated_code (cfg : WasmConfig) (s : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (allocated cfg s p) inst p := by
  have fields := allocated_fields cfg s p
  exact h.transport s _ inst p fields.1 fields.2.1 fields.2.2

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold after tailAfter exitAfter
  simp only [setGlobal,mems_paid]
  apply outputAfter_memory
  rw [mems_paid]
  exact allocated_memory cfg s p hm

theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables := by
  have tail := outputAfter_fields (paid (allocated cfg s p) cfg.regularOpCost 3) cfg.regularOpCost p.memoryIndex
    (allocatedMemory p) p.out687 p.size (cacheWord p)
  have eq : fields (outputAfter (paid (allocated cfg s p) cfg.regularOpCost 3) cfg.regularOpCost p.memoryIndex
      (allocatedMemory p) p.out687 p.size (cacheWord p))=fields (paid (allocated cfg s p) cfg.regularOpCost 3) :=
    fields_pack _ _ ⟨tail.1,tail.2.1,tail.2.2.1⟩
  have all : fields (after cfg s p)=fields s := by
    unfold after tailAfter exitAfter
    rw [fields_global,fields_paid]
    change fields (outputAfter (paid (allocated cfg s p) cfg.regularOpCost 3) cfg.regularOpCost p.memoryIndex
      (allocatedMemory p) p.out687 p.size (cacheWord p))=fields s
    rw [eq,fields_paid]
    exact fields_pack s _ (allocated_fields cfg s p)
  exact ⟨congrArg (fun x=>x.1) all,congrArg (fun x=>x.2.1) all,congrArg (fun x=>x.2.2) all⟩

theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global687) (hv : p.global687.value=.i32 p.sp687) :
    (after cfg s p).globals=s.globals := by
  have tail := (outputAfter_fields (paid (allocated cfg s p) cfg.regularOpCost 3) cfg.regularOpCost p.memoryIndex
    (allocatedMemory p) p.out687 p.size (cacheWord p)).2.2.2
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 p.outerSP) p.global687 hg
  have spEq : p.outerSP+32=p.sp687 := by rw [hn.innerSP];exact UInt32.sub_add_cancel _ _
  unfold after tailAfter exitAfter
  simp only [setGlobal,globals_paid]
  change ((outputAfter (paid (allocated cfg s p) cfg.regularOpCost 3) cfg.regularOpCost p.memoryIndex
    (allocatedMemory p) p.out687 p.size (cacheWord p)).globals.modify p.globalIndex fun g=>{g with value:=.i32 (p.outerSP+32)})=s.globals
  rw [tail,globals_paid,allocated_globals cfg s p hn hg,arguments,globals_paid,guarded,globals_paid,reserved]
  simpa only [setGlobal,globals_paid,spEq,hv] using restore
end WNear.Proofs.AllocateVectorOuter
