import Proofs.StateReadRegisterOuterPhases
import Proofs.StateReadRegisterOuterLengthResult
import Proofs.StateReadRegisterOuterVectorNative
import Proofs.AllocateVectorOuterResult
import Proofs.StateDispatchLengthOuterFrame
import Proofs.StateReadRegisterOuterReadFinalFrame

/-! Exact intermediate memory and installed-code frames for the real f523 callees. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] lengthArguments looked guarded vectorArguments allocated readArguments readDone copyDone copiedMemory AllocateVectorOuter.callAfter StateDispatchLengthOuter.finalStore StateDispatchLengthOuter.callAfter lengthMemory registerMemory branched after

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_charge (s : Store NearState) (cost : Nat) : fields (chargedStore s cost)=fields s := rfl
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).mems=s.mems := rfl
private theorem mems_global (s : Store NearState) (index : Nat) (value : Value) : (setGlobal s index value).mems=s.mems := rfl
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_pack (s t : Store NearState)
    (h : t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables) : fields t=fields s :=
  Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields_unpack (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩

theorem looked_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (looked cfg s p).funcs=s.funcs ∧ (looked cfg s p).modules=s.modules ∧ (looked cfg s p).tables=s.tables := by
  have args := lengthArguments_fields s cfg.regularOpCost p
  have callee := StateDispatchLengthOuter.finalStore_fields cfg
    (StateDispatchLengthOuter.entered (lengthArguments s cfg.regularOpCost p) cfg.regularOpCost) (actualLength p)
  have f : fields (looked cfg s p)=fields (lengthArguments s cfg.regularOpCost p) := by
    simpa only [looked,StateDispatchLengthOuter.callAfter,StateDispatchLengthOuter.entered,fields_charge] using fields_pack _ _ callee
  exact fields_unpack s _ (f.trans (fields_pack _ _ args))

theorem vectorArguments_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (vectorArguments cfg s p).funcs=s.funcs ∧ (vectorArguments cfg s p).modules=s.modules ∧ (vectorArguments cfg s p).tables=s.tables := by
  have f : fields (vectorArguments cfg s p)=fields (looked cfg s p) := by rw [vectorArguments,fields_paid,guarded,fields_paid]
  exact fields_unpack s _ (f.trans (fields_pack _ _ (looked_fields cfg s p)))

theorem allocated_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated cfg s p).funcs=s.funcs ∧ (allocated cfg s p).modules=s.modules ∧ (allocated cfg s p).tables=s.tables := by
  have c := AllocateVectorOuter.callAfter_fields cfg (vectorArguments cfg s p) (actualVector p)
  have a := vectorArguments_fields cfg s p
  unfold allocated
  exact ⟨c.1.trans a.1,c.2.1.trans a.2.1,c.2.2.trans a.2.2⟩

theorem readArguments_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (readArguments cfg s p).funcs=s.funcs ∧ (readArguments cfg s p).modules=s.modules ∧ (readArguments cfg s p).tables=s.tables := by
  apply fields_unpack
  rw [readArguments,fields_paid]
  exact fields_pack _ _ (allocated_fields cfg s p)

theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    (allocated cfg s p).mems[p.memoryIndex]?=some (readInputMemory p) := by
  have lm := looked_memory cfg s limits inst height callers p extra hn ha hcode hm hg hr hd
  unfold allocated readInputMemory
  have vm : (vectorArguments cfg s p).mems[(actualVector p).memoryIndex]?=some (actualVector p).memory := by
    simpa only [actualVector,vectorMemoryTemplate] using (show (vectorArguments cfg s p).mems[p.memoryIndex]?=some (lengthMemory p) from by
      rw [vectorArguments,mems_paid,guarded,mems_paid]
      exact lm)
  have result := AllocateVectorOuter.callAfter_memory cfg (vectorArguments cfg s p) (actualVector p) vm
  have index : (actualVector p).memoryIndex=p.memoryIndex := rfl
  rw [index] at result
  exact result

theorem readDone_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    (readDone cfg s p).mems[p.memoryIndex]?=some (readFinalMemory p) := by
  unfold readDone
  apply read_call_memory cfg _ p hcode.prefixCode.memoryIndex
  rw [readArguments,mems_paid]
  exact allocated_memory cfg s limits inst height callers p extra hn ha hcode hm hg hr hd

theorem copyDone_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : (readDone cfg s p).mems[p.memoryIndex]?=some (readFinalMemory p)) :
    (copyDone cfg s p).mems[p.memoryIndex]?=some (copiedMemory p) := by
  have high := storeI32_memory (paid (readDone cfg s p) cfg.regularOpCost 10) p.memoryIndex (p.out523+8).toNat
    (readFinalMemory p) (readI32 (readFinalMemory p) (scratch p+32+8).toNat) (by rw [mems_paid];exact hm)
  unfold copyDone copied copiedMemory finalMemory copyLow
  apply storeI64_memory
  rw [mems_paid]
  simpa only [copyHigh,firstMemory] using high
theorem looked_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (hg : s.globals[p.globalIndex]?=some p.global523) :
    (looked cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  let active := StateDispatchLengthOuter.entered (lengthArguments s cfg.regularOpCost p) cfg.regularOpCost
  have ag : active.globals[(actualLength p).inner.globalIndex]?=some (actualLength p).global :=
    lengthArguments_global s cfg.regularOpCost p hg
  have av : (actualLength p).global.value=.i32 (actualLength p).sp := rfl
  have call := StateDispatchLengthOuter.finalStore_globals cfg active (actualLength p) ag av (length_native p hn)
  have args : (lengthArguments s cfg.regularOpCost p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
    simp only [lengthArguments,globals_paid,registerStore,storeI64_globals,reserved,setGlobal]
  unfold looked StateDispatchLengthOuter.callAfter
  exact call.trans args

theorem vectorArguments_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (hg : s.globals[p.globalIndex]?=some p.global523) :
    (vectorArguments cfg s p).globals[p.globalIndex]?=some (actualVector p).global687 := by
  rw [vectorArguments,globals_paid,guarded,globals_paid,looked_globals cfg s p hn hg]
  simp only [setGlobal,Array.getElem?_modify,hg,Option.map_some]
  have eq : (actualVector p).global687={p.global523 with value:=.i32 (scratch p)} := by
    change p.global687=_
    rw [hn.vectorGlobal,hn.vectorSP]
  rw [eq]
  simp only [ite_true]

theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (ha : p.allocator=1074896) (hg : s.globals[p.globalIndex]?=some p.global523) :
    (allocated cfg s p).globals=(setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
  have gg := vectorArguments_global cfg s p hn hg
  have index : (actualVector p).globalIndex=p.globalIndex := rfl
  have vg : (vectorArguments cfg s p).globals[(actualVector p).globalIndex]?=some (actualVector p).global687 := by
    rw [index];exact gg
  have vv : (actualVector p).global687.value=.i32 (actualVector p).sp687 := by
    change p.global687.value=.i32 p.sp687
    rw [hn.vectorGlobal]
  have callee := AllocateVectorOuter.callAfter_globals cfg (vectorArguments cfg s p) (actualVector p) (vector_native p hn ha) vg vv
  unfold allocated
  rw [callee,vectorArguments,globals_paid,guarded,globals_paid]
  exact looked_globals cfg s p hn hg
theorem readArguments_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (ha : p.allocator=1074896) (hg : s.globals[p.globalIndex]?=some p.global523) :
    (readArguments cfg s p).globals[p.globalIndex]?=some {p.global523 with value:=.i32 (scratch p)} := by
  rw [readArguments,globals_paid,allocated_globals cfg s p hn ha hg]
  simp only [setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : (readDone cfg s p).mems[p.memoryIndex]?=some (readFinalMemory p)) :
    (after cfg s p).mems[p.memoryIndex]?=some (copiedMemory p) := by
  rw [after,mems_global,mems_paid,branched,mems_charge]
  exact copyDone_memory cfg s p hm
end WNear.Proofs.StateReadRegisterOuter
