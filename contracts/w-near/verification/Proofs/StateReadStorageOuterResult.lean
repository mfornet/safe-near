import Proofs.StateReadStorageOuterOutputFrame
import Proofs.StateReadStorageOuterRegisterMemory
import Proofs.StateReadStorageOuterEntry

/-! Exact full f548 memory, original global/code frames, and closed selected-path ledger. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] after converted optionArguments callAfter entered finalMemory actualRegister
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems := rfl

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hd : callers.length+4<limits.maxCallDepth) :
    (after cfg s p ctx key).mems[p.memoryIndex]?=some (finalMemory p) := by
  have reg := registered_memory cfg s limits inst height callers p ctx key extra hn ha hcode hm hg hd
  have before : (optionArguments cfg s p ctx key).mems[p.memoryIndex]?=some (registeredMemory p) := by
    rw [optionArguments,mems_paid];exact reg
  have result := StateReadResult.callAfter_memory (optionArguments cfg s p ctx key) cfg.regularOpCost
    p.memoryIndex (registeredMemory p) p.out548 (scratch p+16) before
  rw [after,mems_global,mems_paid,converted]
  unfold finalMemory
  exact result

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hd : callers.length+4<limits.maxCallDepth) :
    (callAfter cfg s p ctx key).mems[p.memoryIndex]?=some (finalMemory p) := by
  have code : Code (entered s cfg.regularOpCost) inst p extra :=
    hcode.transport s _ inst p extra (by unfold entered;rfl) (by unfold entered;rfl) (by unfold entered;rfl)
  have am : (entered s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory := by unfold entered;exact hm
  have ag : (entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.global548 := by unfold entered;exact hg
  unfold callAfter
  exact after_memory cfg _ limits inst height callers p ctx key extra hn ha code am ag hd

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (callAfter cfg s p ctx key).funcs=s.funcs ∧ (callAfter cfg s p ctx key).modules=s.modules ∧
    (callAfter cfg s p ctx key).tables=s.tables := by
  unfold callAfter
  simpa only [entered,chargedStore] using after_fields cfg (entered s cfg.regularOpCost) p ctx key

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (hn : Native p) (ha : p.allocator=1074896)
    (hg : s.globals[p.globalIndex]?=some p.global548) (hv : p.global548.value=.i32 p.sp548) :
    (callAfter cfg s p ctx key).globals=s.globals := by
  have ag : (entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.global548 := by unfold entered;exact hg
  unfold callAfter
  simpa only [entered,chargedStore] using after_globals cfg (entered s cfg.regularOpCost) p ctx key hn ha ag hv

theorem call_ledger (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    bodyCost p+12=13*p.bytes.length+1848 ∧ bodySteps p+2=12*p.bytes.length+1358 := by
  have cost := StateReadRegisterOuter.bodyCost_eq_bytes (actualRegister p) (register_native p hn ha)
  have steps := StateReadRegisterOuter.bodySteps_eq_bytes (actualRegister p) (register_native p hn ha)
  have bytes : (actualRegister p).bytes=p.bytes := by simp only [actualRegister,registerTemplate]
  unfold bodyCost bodySteps
  rw [cost,steps,bytes]
  omega
end WNear.Proofs.StateReadStorageOuter
