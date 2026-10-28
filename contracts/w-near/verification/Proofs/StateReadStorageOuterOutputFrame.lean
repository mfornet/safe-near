import Proofs.StateReadStorageOuterRegisteredFrame
import Proofs.StateReadStorageOuterResultOutput

/-! Exact code and original global-array restoration at the complete f548 endpoint. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] after converted optionArguments registered registerArguments guarded
  storageArguments setupStore highStore reserved
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem tables_paid (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem converted_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (converted cfg s p ctx key).funcs=s.funcs ∧ (converted cfg s p ctx key).modules=s.modules ∧
    (converted cfg s p ctx key).tables=s.tables ∧
    (converted cfg s p ctx key).globals=(registered cfg s p ctx key).globals := by
  have call := StateReadResult.callAfter_fields (optionArguments cfg s p ctx key) cfg.regularOpCost
    p.memoryIndex (registeredMemory p) p.out548 (scratch p+16)
  have before := registered_fields cfg s p ctx key
  unfold converted
  rw [call.1,call.2.1,call.2.2.1,call.2.2.2]
  simp only [optionArguments,funcs_paid,modules_paid,tables_paid,globals_paid]
  exact ⟨before.1,before.2.1,before.2.2,trivial⟩

theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (after cfg s p ctx key).funcs=s.funcs ∧ (after cfg s p ctx key).modules=s.modules ∧
    (after cfg s p ctx key).tables=s.tables := by
  simp only [after,setGlobal,funcs_paid,modules_paid,tables_paid]
  have h := converted_fields cfg s p ctx key
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (hn : Native p) (ha : p.allocator=1074896)
    (hg : s.globals[p.globalIndex]?=some p.global548) (hv : p.global548.value=.i32 p.sp548) :
    (after cfg s p ctx key).globals=s.globals := by
  have convert := (converted_fields cfg s p ctx key).2.2.2
  have reg := registered_globals cfg s p ctx key hn ha hg
  have st := stored_globals cfg s p ctx key hn hg
  have setup : (storageArguments s cfg.regularOpCost p).globals=
      (setGlobal s p.globalIndex (.i32 (scratch p))).globals := by
    rw [storageArguments,globals_paid,setupStore,storeI32_globals,globals_paid,
      highStore,storeI32_globals,globals_paid,reserved]
    simp only [setGlobal,globals_paid]
  unfold after
  simp only [setGlobal,globals_paid]
  rw [convert,reg,registerArguments,globals_paid,guarded,globals_paid,st,setup]
  have restore := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global548 hg
  simpa only [setGlobal,hv] using restore
end WNear.Proofs.StateReadStorageOuter
