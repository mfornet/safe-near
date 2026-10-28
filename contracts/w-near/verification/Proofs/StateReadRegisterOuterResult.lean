import Proofs.StateReadRegisterOuterCall
import Proofs.StateReadRegisterOuterOutputRecord
import Proofs.StateReadRegisterOuterOutputPayload
import Proofs.StateReadRegisterOuterFunctionalHost
import Proofs.StateReadRegisterOuterLedger

/-! Typed f523 resource endpoints, exact sequential memory, canonical record
under its precise copy separation, and original register payload contents. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StateReadRegister (functionalHostView view_mask view_charge)
set_option maxRecDepth 16384
attribute [local irreducible] entered callAfter after readDone copiedMemory

private theorem entered_mems (s : Store NearState) (op : Nat) : (entered s op).mems=s.mems := by unfold entered;rfl
private theorem entered_globals (s : Store NearState) (op : Nat) : (entered s op).globals=s.globals := by unfold entered;rfl
private theorem entered_registers (s : Store NearState) (op : Nat) : (entered s op).host.registers=s.host.registers := by unfold entered;rfl
private theorem entered_code (s : Store NearState) (op inst : Nat) (p : Layout) (extra : Nat)
    (hc : Code s inst p extra) : Code (entered s op) inst p extra := by
  unfold entered
  exact hc.transport s _ inst p extra rfl rfl rfl

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (copiedMemory p) := by
  let active := entered s cfg.regularOpCost
  have am : active.mems[p.memoryIndex]?=some p.memory := by rw [entered_mems];exact hm
  have ag : active.globals[p.globalIndex]?=some p.global523 := by rw [entered_globals];exact hg
  have ar : active.host.registers p.register.toNat=some p.bytes := by rw [entered_registers];exact hr
  have cd := entered_code s cfg.regularOpCost inst p extra hcode
  unfold callAfter
  apply after_memory
  exact readDone_memory cfg active limits inst height callers p extra hn ha cd am ag ar hd

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables := by
  unfold callAfter
  have h := after_fields cfg (entered s cfg.regularOpCost) p
  have e : (entered s cfg.regularOpCost).funcs=s.funcs ∧
      (entered s cfg.regularOpCost).modules=s.modules ∧ (entered s cfg.regularOpCost).tables=s.tables := by
    unfold entered
    exact ⟨rfl,rfl,rfl⟩
  exact ⟨h.1.trans e.1,h.2.1.trans e.2.1,h.2.2.trans e.2.2⟩

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (ha : p.allocator=1074896) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hv : p.global523.value=.i32 p.sp523) : (callAfter cfg s p).globals=s.globals := by
  have ag : (entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.global523 := by rw [entered_globals];exact hg
  unfold callAfter
  rw [after_globals cfg (entered s cfg.regularOpCost) p hn ha ag hv,entered_globals]

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView s.host (callAfter cfg s p).host=s.host := by
  unfold callAfter
  have h := view_mask s.host (entered s cfg.regularOpCost).host _
    (after_functional_host cfg (entered s cfg.regularOpCost) p)
  have entry : functionalHostView s.host (entered s cfg.regularOpCost).host=s.host := by
    rw [entered,view_charge,view_charge]
    rfl
  exact h.trans entry

theorem callAfter_actionProfile (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).host.actionProfile=s.host.actionProfile := by
  have eq := congrArg NearState.actionProfile (callAfter_functional_host cfg s p)
  exact eq

/-- Actual local-call activation and normal leave yield the closed selected-path ledger. -/
theorem call_ledger (p : Layout) (hn : Native p) :
    bodyCost p+11=13*p.bytes.length+1511 ∧ bodySteps p+2=12*p.bytes.length+1127 := by
  rw [bodyCost_eq_bytes p hn,bodySteps_eq_bytes p hn]
  omega

theorem callAfter_output (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth)
    (hs : (scratch p).toNat+40≤(p.out523+8).toNat ∨ (p.out523+8).toNat+4≤(scratch p).toNat+32) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (copiedMemory p) ∧
    readI32 (copiedMemory p) p.out523.toNat=AllocateVector.result (actualVector p).toVector ∧
    readI32 (copiedMemory p) (p.out523.toNat+4)=p.size ∧
    readI32 (copiedMemory p) (p.out523.toNat+8)=p.size ∧
    ∀ i, i<p.bytes.length →
      (copiedMemory p).read8 ((AllocateVector.result (actualVector p).toVector).toNat+i)=p.bytes[i]! := by
  have record := copiedMemory_record p hn ha hs
  exact ⟨callAfter_memory cfg s limits inst height callers p extra hn ha hcode hm hg hr hd,
    record.1,record.2.1,record.2.2,copiedMemory_payload p hn ha⟩
end WNear.Proofs.StateReadRegisterOuter
