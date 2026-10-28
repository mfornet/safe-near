import Proofs.StateDecodePrefixPhases
import Proofs.StateDecodePrefixEarlyFrame
import Proofs.StateDecodeVectorCopyFrame
import Proofs.StateDecodePrefixOutputResult

/-! Installed arrays and stack-global restoration through the whole accepted316 path. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem input_gi (p : Layout) (q : StateDecodeVectorCopy.Layout) (hd : AcceptedDomain p q) :
    (allocationInput p q).globalIndex=p.globalIndex := by unfold allocationInput;exact hd.globalIndex
private theorem input_global (p : Layout) (q : StateDecodeVectorCopy.Layout) (hd : AcceptedDomain p q) :
    (allocationInput p q).globalVector={p.global with value:=.i32 (scratch p)} := by unfold allocationInput;exact hd.global
private theorem input_sp (p : Layout) (q : StateDecodeVectorCopy.Layout) (hd : AcceptedDomain p q) :
    (allocationInput p q).spVector=scratch p := by unfold allocationInput;exact hd.sp
private theorem drop_fields (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch slice n : UInt32) :
    (dropPayloadAfter cfg s i m scratch slice n).funcs=s.funcs ∧
    (dropPayloadAfter cfg s i m scratch slice n).modules=s.modules ∧
    (dropPayloadAfter cfg s i m scratch slice n).tables=s.tables := by
  have h:=StateDecodeSlices.callAfter_fields true (paid s cfg.regularOpCost 9) cfg.regularOpCost i m (scratch+8)
    (readI32 m slice.toNat) (readI32 m (slice.toNat+4)) n
  unfold dropPayloadAfter
  refine ⟨?_,?_,?_⟩
  · exact h.1.trans (paid_funcs s cfg.regularOpCost 9)
  · exact h.2.1.trans (paid_modules s cfg.regularOpCost 9)
  · exact h.2.2.1.trans (paid_tables s cfg.regularOpCost 9)
private theorem drop_globals (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch slice n : UInt32) :
    (dropPayloadAfter cfg s i m scratch slice n).globals=s.globals := by
  have h:=StateDecodeSlices.callAfter_fields true (paid s cfg.regularOpCost 9) cfg.regularOpCost i m (scratch+8)
    (readI32 m slice.toNat) (readI32 m (slice.toNat+4)) n
  unfold dropPayloadAfter
  exact h.2.2.2.trans (paid_globals s cfg.regularOpCost 9)
attribute [local irreducible] allocationInput copyArguments allocated dropped outputted after allocatedMemory

theorem copyArguments_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (copyArguments cfg s p).funcs=s.funcs ∧(copyArguments cfg s p).modules=s.modules ∧(copyArguments cfg s p).tables=s.tables ∧
    (copyArguments cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  simpa only [copyArguments,paid_funcs,paid_modules,paid_tables,paid_globals] using payloadPrefix_fields cfg s p

theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (allocated cfg s p q).funcs=s.funcs ∧(allocated cfg s p q).modules=s.modules ∧(allocated cfg s p q).tables=s.tables := by
  have h:=StateDecodeVectorCopy.callAfter_fields cfg (copyArguments cfg s p) (allocationInput p q)
  have a:=copyArguments_fields cfg s p
  unfold allocated
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.trans a.2.2.1⟩

theorem copyArguments_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) :
    (copyArguments cfg s p).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
  rw [(copyArguments_fields cfg s p).2.2.2]
  simp only [reservedPrefix,setGlobal,paid_globals,Array.getElem?_modify,hg,Option.map_some,ite_true]

theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hg : s.globals[p.globalIndex]?=some p.global) :
    (allocated cfg s p q).globals=(copyArguments cfg s p).globals := by
  have before : (copyArguments cfg s p).globals[(allocationInput p q).globalIndex]?=some (allocationInput p q).globalVector := by
    rw[input_gi p q hd,input_global p q hd]
    exact copyArguments_global cfg s p hg
  have sp : (allocationInput p q).globalVector.value=.i32 (allocationInput p q).spVector := by
    rw[input_global p q hd,input_sp p q hd]
  unfold allocated
  exact StateDecodeVectorCopy.callAfter_globals cfg (copyArguments cfg s p) (allocationInput p q)
    (allocation_copy_native p q hn hd.toAllocationDomain) before sp

theorem dropped_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (dropped cfg s p q).funcs=s.funcs ∧(dropped cfg s p q).modules=s.modules ∧(dropped cfg s p q).tables=s.tables := by
  have h:=drop_fields cfg (allocated cfg s p q) p.memoryIndex (allocatedMemory p q) (scratch p) p.slice (count p)
  have a:=allocated_fields cfg s p q
  unfold dropped
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.trans a.2.2⟩

theorem dropped_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (dropped cfg s p q).globals=(allocated cfg s p q).globals := by
  unfold dropped
  exact drop_globals cfg (allocated cfg s p q) p.memoryIndex (allocatedMemory p q) (scratch p) p.slice (count p)

theorem outputted_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (outputted cfg s p q).funcs=s.funcs ∧(outputted cfg s p q).modules=s.modules ∧(outputted cfg s p q).tables=s.tables := by
  have h:=Output.after_fields (dropped cfg s p q) cfg.regularOpCost (outputLayout p q)
  have a:=dropped_fields cfg s p q
  unfold outputted
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.1.trans a.2.2⟩

theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (after cfg s p q).funcs=s.funcs ∧(after cfg s p q).modules=s.modules ∧(after cfg s p q).tables=s.tables := by
  simpa only [after,setGlobal,paid_funcs,paid_modules,paid_tables] using outputted_fields cfg s p q

theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after cfg s p q).globals=s.globals := by
  have out : (outputted cfg s p q).globals=(dropped cfg s p q).globals := by
    unfold outputted
    exact (Output.after_fields (dropped cfg s p q) cfg.regularOpCost (outputLayout p q)).2.2.2
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  simp only [after,setGlobal,paid_globals,out,dropped_globals,allocated_globals cfg s p q hn hd hg,
    (copyArguments_fields cfg s p).2.2.2,reservedPrefix,setGlobal,paid_globals,←hv]
  exact restore
end WNear.Proofs.StateDecodePrefix
