import Proofs.StateDecodeRawPhases
import Proofs.StateDecodeRawCopyFrame
import Proofs.StateDecodeRawCopyGlobals
import Proofs.StateDecodeRawFinishResources
import Proofs.AllocateVectorFrame

/-! Original resources through the actual f767 layout, allocation and output. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem entered_mems (s : Store NearState) (op : Nat) : (entered769 s op).mems=s.mems:=rfl
private theorem entered_globals (s : Store NearState) (op : Nat) : (entered769 s op).globals=s.globals:=rfl
private theorem global_mems (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems:=rfl
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem entered_funcs (s : Store NearState) (op : Nat) : (entered769 s op).funcs=s.funcs:=rfl
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem entered_modules (s : Store NearState) (op : Nat) : (entered769 s op).modules=s.modules:=rfl
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem entered_tables (s : Store NearState) (op : Nat) : (entered769 s op).tables=s.tables:=rfl
attribute [local irreducible] laidOutRaw layoutArgumentsRaw reservedRaw alignedRaw checkedRaw flagCheckedRaw argumentsRaw
  allocatedRaw cachedRaw afterRaw callAfter769 after769 entered769 memory769 finalMemory laidOutMemory

theorem laidOutRaw_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (laidOutRaw s op p).mems[p.memoryIndex]?=some (laidOutMemory p) := by
  have input : (layoutArgumentsRaw s op p).mems[p.memoryIndex]?=some p.memory := by
    rw [layoutArgumentsRaw,paid_mems,reservedRaw,global_mems,paid_mems];exact hm
  unfold laidOutRaw laidOutMemory
  exact AllocateLayoutWrapper.called_memory (layoutArgumentsRaw s op p) op (layout752 p) input

theorem laidOutRaw_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) :
    (laidOutRaw s op p).globals=(reservedRaw s op p).globals := by
  have input : (layoutArgumentsRaw s op p).globals[p.globalIndex]?=some (layout752 p).global := by
    simp only [layoutArgumentsRaw,paid_globals,reservedRaw,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true,layout752]
  have h:=AllocateLayoutWrapper.called_globals (layoutArgumentsRaw s op p) op (layout752 p) input rfl
  simpa only [laidOutRaw,layoutArgumentsRaw,paid_globals] using h

theorem argumentsRaw_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (argumentsRaw s op p).mems[p.memoryIndex]?=some (laidOutMemory p) := by
  simp only [argumentsRaw,flagCheckedRaw,checkedRaw,alignedRaw,paid_mems]
  exact laidOutRaw_memory s op p hm

theorem argumentsRaw_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) :
    (argumentsRaw s op p).globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)} := by
  simp only [argumentsRaw,flagCheckedRaw,checkedRaw,alignedRaw,paid_globals,laidOutRaw_globals s op p hg,
    reservedRaw,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]

theorem allocatedRaw_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocatedRaw cfg s p).mems[p.memoryIndex]?=some (memory769 p) := by
  have input:=argumentsRaw_memory s cfg.regularOpCost p hm
  have entered : (entered769 (argumentsRaw s cfg.regularOpCost p) cfg.regularOpCost).mems[p.memoryIndex]?=some (laidOutMemory p) := by
    rw [entered_mems];exact input
  simpa only [allocatedRaw,callAfter769] using after769_memory cfg (entered769 (argumentsRaw s cfg.regularOpCost p) cfg.regularOpCost) p hn entered

theorem allocatedRaw_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) :
    (allocatedRaw cfg s p).globals=(argumentsRaw s cfg.regularOpCost p).globals := by
  have input:=argumentsRaw_global s cfg.regularOpCost p hg
  have entered : (entered769 (argumentsRaw s cfg.regularOpCost p) cfg.regularOpCost).globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)} := by
    rw [entered_globals];exact input
  simpa only [allocatedRaw,callAfter769,entered_globals] using after769_globals cfg (entered769 (argumentsRaw s cfg.regularOpCost p) cfg.regularOpCost) p hn entered

theorem cachedRaw_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (cachedRaw cfg s p).mems[p.memoryIndex]?=some (memory769 p) := by
  rw [cachedRaw,paid_mems];exact allocatedRaw_memory cfg s p hn hm

theorem cachedRaw_global (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) :
    (cachedRaw cfg s p).globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)} := by
  rw [cachedRaw,paid_globals,allocatedRaw_globals cfg s p hn hg]
  exact argumentsRaw_global s cfg.regularOpCost p hg
theorem afterRaw_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (afterRaw cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold afterRaw finalMemory
  exact finished_memory (cachedRaw cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memory769 p)
    p.outRaw (cachedPointer p) (cachedLength p) (scratch p) (cachedRaw_memory cfg s p hn hm)

theorem afterRaw_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) (hv : p.globalRaw.value=.i32 p.spRaw) :
    (afterRaw cfg s p).globals=s.globals := by
  have h:=finished_globals (cachedRaw cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memory769 p)
    p.outRaw (cachedPointer p) (cachedLength p) (scratch p)
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.globalRaw hg
  have sp : scratch p+32=p.spRaw := UInt32.sub_add_cancel _ _
  unfold afterRaw
  rw [h]
  simp only [setGlobal,cachedRaw,paid_globals,allocatedRaw_globals cfg s p hn hg,
    argumentsRaw,flagCheckedRaw,checkedRaw,alignedRaw,paid_globals,laidOutRaw_globals s cfg.regularOpCost p hg]
  rw [sp,←hv]
  simpa only [reservedRaw,setGlobal,paid_globals] using restore
theorem laidOutRaw_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (laidOutRaw s op p).funcs=s.funcs ∧ (laidOutRaw s op p).modules=s.modules ∧ (laidOutRaw s op p).tables=s.tables := by
  have h:=AllocateLayoutWrapper.called_fields (layoutArgumentsRaw s op p) op (layout752 p)
  have a : (layoutArgumentsRaw s op p).funcs=s.funcs ∧ (layoutArgumentsRaw s op p).modules=s.modules ∧ (layoutArgumentsRaw s op p).tables=s.tables := by
    simp only [layoutArgumentsRaw,reservedRaw,setGlobal,paid_funcs,paid_modules,paid_tables,and_self]
  unfold laidOutRaw
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.trans a.2.2⟩

theorem argumentsRaw_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (argumentsRaw s op p).funcs=s.funcs ∧ (argumentsRaw s op p).modules=s.modules ∧ (argumentsRaw s op p).tables=s.tables := by
  simp only [argumentsRaw,flagCheckedRaw,checkedRaw,alignedRaw,paid_funcs,paid_modules,paid_tables]
  exact laidOutRaw_fields s op p

theorem allocatedRaw_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocatedRaw cfg s p).funcs=s.funcs ∧ (allocatedRaw cfg s p).modules=s.modules ∧ (allocatedRaw cfg s p).tables=s.tables := by
  have h:=after769_fields cfg (entered769 (argumentsRaw s cfg.regularOpCost p) cfg.regularOpCost) p
  have a:=argumentsRaw_fields s cfg.regularOpCost p
  simp only [entered_funcs,entered_modules,entered_tables] at h
  unfold allocatedRaw callAfter769
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.trans a.2.2⟩

theorem afterRaw_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (afterRaw cfg s p).funcs=s.funcs ∧ (afterRaw cfg s p).modules=s.modules ∧ (afterRaw cfg s p).tables=s.tables := by
  have h:=finished_fields (cachedRaw cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memory769 p)
    p.outRaw (cachedPointer p) (cachedLength p) (scratch p)
  have a : (cachedRaw cfg s p).funcs=s.funcs ∧ (cachedRaw cfg s p).modules=s.modules ∧ (cachedRaw cfg s p).tables=s.tables := by
    simp only [cachedRaw,paid_funcs,paid_modules,paid_tables]
    exact allocatedRaw_fields cfg s p
  unfold afterRaw
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.trans a.2.2⟩
end WNear.Proofs.StateDecodeRaw
