import Proofs.AllocateVectorGas
import Proofs.AllocateVectorNative
import Proofs.AllocateLayoutWrapperHost

/-! Exact686 sequential memory, installed code and globals across685/690. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] reserved arguments laidOut guarded selected allocateArguments allocated cached joined nonzero recorded restored after resultMemory layout690 actualRecord AllocateRecordCopy.callAfter AllocateRecordCopy.resultMemory readI32 writeI32
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
 theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (arguments s op p).mems[p.memoryIndex]?=some p.memory := by
  rw [arguments,mems_paid,reserved,setGlobal,mems_paid];exact hm
 theorem laidOut_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (laidOut s op p).mems[p.memoryIndex]?=some (laidOutMemory p) := by
  unfold laidOut laidOutMemory
  exact AllocateLayoutWrapper.called_memory (arguments s op p) op (layout685 p) (arguments_memory s op p hm)
 theorem allocateArguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (allocateArguments s op p).mems[p.memoryIndex]?=some (laidOutMemory p) := by
  rw [allocateArguments,mems_paid,selected,mems_paid,guarded,mems_paid]
  exact laidOut_memory s op p hm
 theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (allocated cfg s p).mems[p.memoryIndex]?=some (resultMemory p) := by
  have initial : (allocateArguments s cfg.regularOpCost p).mems[(layout690 p).inner.memoryIndex]?=some (layout690 p).inner.memory := by
    simpa only [layout690,actualRecord] using allocateArguments_memory s cfg.regularOpCost p hm
  have h := AllocateRecordCopy.callAfter_memory cfg (allocateArguments s cfg.regularOpCost p) (layout690 p) initial
  have index : (layout690 p).inner.memoryIndex=p.memoryIndex := by simp only [layout690,actualRecord]
  rw [index] at h
  simpa only [allocated,resultMemory] using h
 theorem nonzero_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (nonzero cfg s p).mems[p.memoryIndex]?=some (resultMemory p) := by
  rw [nonzero,mems_paid,joined,mems_paid,cached,mems_paid]
  exact allocated_memory cfg s p hm
 theorem recordStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32)
    (hm : s.mems[index]?=some memory) :
    (recordStore s op index memory out pointer size).mems[index]?=some (recordMemory memory out pointer size) := by
  have first := storeI32_memory (paid s op 3) index out.toNat memory pointer (by rw [mems_paid];exact hm)
  unfold recordStore recordMemory
  apply storeI32_memory
  rw [mems_paid];exact first
 theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) : (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  rw [after,chargedStore,restored,setGlobal,mems_paid]
  unfold recorded finalMemory
  apply recordStore_memory
  exact nonzero_memory cfg s p hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_global (s : Store NearState) (i : Nat) (v : Value) : fields (setGlobal s i v)=fields s := rfl
private theorem fields_charge (s : Store NearState) (n : Nat) : fields (chargedStore s n)=fields s := rfl
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s := rfl
private theorem fields_pack (s t : Store NearState) (h : t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables) : fields t=fields s :=
  Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields_layout (s : Store NearState) (op : Nat) (p : AllocateLayoutWrapper.Layout) :
    fields (AllocateLayoutWrapper.called s op p)=fields s := fields_pack s _ (AllocateLayoutWrapper.called_fields s op p)
private theorem fields_copy (cfg : WasmConfig) (s : Store NearState) (p : AllocateRecordCopy.Layout) :
    fields (AllocateRecordCopy.callAfter cfg s p)=fields s := fields_pack s _ (AllocateRecordCopy.callAfter_fields cfg s p)
private theorem fields_arguments (s : Store NearState) (op : Nat) (p : Layout) : fields (arguments s op p)=fields s := by
  rw [arguments,fields_paid,reserved,fields_global,fields_paid]
private theorem fields_laidOut (s : Store NearState) (op : Nat) (p : Layout) : fields (laidOut s op p)=fields s := by
  rw [laidOut,fields_layout,fields_arguments]
private theorem fields_allocateArguments (s : Store NearState) (op : Nat) (p : Layout) : fields (allocateArguments s op p)=fields s := by
  rw [allocateArguments,fields_paid,selected,fields_paid,guarded,fields_paid,fields_laidOut]
 theorem allocateArguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (allocateArguments s op p).funcs=s.funcs ∧ (allocateArguments s op p).modules=s.modules ∧ (allocateArguments s op p).tables=s.tables := by
  have eq := fields_allocateArguments s op p
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩
 theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).funcs=s.funcs ∧ (allocated cfg s p).modules=s.modules ∧ (allocated cfg s p).tables=s.tables := by
  have eq : fields (allocated cfg s p)=fields s := by rw [allocated,fields_copy,fields_allocateArguments]
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩
 theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧ (after cfg s p).tables=s.tables := by
  have eq : fields (after cfg s p)=fields s := by
    rw [after,fields_charge,restored,fields_global,fields_paid,recorded,recordStore,fields_store,fields_paid,
      fields_store,fields_paid,nonzero,fields_paid,joined,fields_paid,cached,fields_paid,allocated,fields_copy,fields_allocateArguments]
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩

 theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.outerGlobal) :
    (arguments s op p).globals[p.globalIndex]?=some {p.outerGlobal with value:=.i32 (reservedSP p)} := by
  rw [arguments,globals_paid,reserved]
  simp only [setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some]
  rfl
 theorem laidOut_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.outerGlobal) : (laidOut s op p).globals=(arguments s op p).globals := by
  unfold laidOut
  exact AllocateLayoutWrapper.called_globals (arguments s op p) op (layout685 p) (arguments_global s op p hg) rfl
 theorem allocateArguments_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.outerGlobal) : (allocateArguments s op p).globals=(arguments s op p).globals := by
  rw [allocateArguments,globals_paid,selected,globals_paid,guarded,globals_paid]
  exact laidOut_globals s op p hg
 theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.outerGlobal) : (allocated cfg s p).globals=(arguments s cfg.regularOpCost p).globals := by
  have ga : (allocateArguments s cfg.regularOpCost p).globals[p.globalIndex]?=some {p.outerGlobal with value:=.i32 (reservedSP p)} := by
    rw [allocateArguments_globals s cfg.regularOpCost p hg]
    exact arguments_global s cfg.regularOpCost p hg
  have h := AllocateRecordCopy.callAfter_globals cfg (allocateArguments s cfg.regularOpCost p) (layout690 p) (copy_native p hn)
    (by simpa only [layout690,actualRecord] using ga) (by simp only [layout690])
  rw [allocateArguments_globals s cfg.regularOpCost p hg] at h
  simpa only [allocated] using h
private theorem globals_charge (s : Store NearState) (n : Nat) : (chargedStore s n).globals=s.globals := rfl
private theorem globals_global (s : Store NearState) (index : Nat) (v : Value) :
    (setGlobal s index v).globals=s.globals.modify index (fun g=>{g with value:=v}) := rfl
private theorem globals_record (s : Store NearState) (op index : Nat) (m : Memory) (out pointer size : UInt32) :
    (recordStore s op index m out pointer size).globals=s.globals := by
  rw [recordStore,storeI32_globals,globals_paid,storeI32_globals,globals_paid]
 theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.outerGlobal) (hv : p.outerGlobal.value=.i32 p.outerSP) :
    (after cfg s p).globals=s.globals := by
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (reservedSP p)) p.outerGlobal hg
  rw [after,globals_charge,restored,globals_global,globals_paid,recorded,globals_record,
    nonzero,globals_paid,joined,globals_paid,cached,globals_paid,allocated_globals cfg s p hn hg,
    arguments,globals_paid,reserved,globals_global,globals_paid]
  simpa only [setGlobal,hv] using restore
end WNear.Proofs.AllocateVector
