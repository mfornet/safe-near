import Proofs.StateReadStorageOuterMemory

/-! Actual459 writes precisely register zero, preserving all other registers.
These projections concern its computed state; its closed WP supplies execution. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] checked arguments returned finalStore callAfter

private theorem registers_of_mask (before actual : NearState)
    (h : {actual with gas:=before.gas,gasProfile:=before.gasProfile}=before) : actual.registers=before.registers := by
  have eq := congrArg NearState.registers h
  exact eq
private theorem registers_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.registers=s.host.registers := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem registers_charge (s : Store NearState) (amount : Nat) : (chargedStore s amount).host.registers=s.host.registers := rfl
private theorem registers_global (s : Store NearState) (index : Nat) (value : Value) : (setGlobal s index value).host.registers=s.host.registers := rfl
private theorem registers_finish (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (StateDispatchStorageFinish.after s op index sp).host.registers=s.host.registers := by
  simp only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.afterReturn,
    StateDispatchLengthFinish.afterReturn,StateDispatchStorageFinish.returned,StateDispatchReturn.callAfter,
    StateDispatchReturn.entered,StateDispatchReturn.after,StateDispatchReturn.suffixAfter,StateDispatchReturn.reserved,
    registers_paid,registers_global,registers_charge]
private theorem registers_cleanup (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (StateDispatchStorageCleanup.after s op index counter memory).host.registers=s.host.registers := by
  exact registers_of_mask s.host _ (StateDispatchStorageCleanup.after_host s op index counter memory)

theorem returned_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (returned cfg s p ctx key value).host.registers=fun i=>if i=0 then some value else s.host.registers i := by
  have checkedRegs : (checked s cfg.regularOpCost p).host.registers=s.host.registers :=
    registers_of_mask s.host _ (checked_host s cfg.regularOpCost p)
  unfold returned
  rw [StateReadStorage.callAfter_registers]
  simp only [show (0:UInt64)≠u64Max by decide,ite_false,show (0:UInt64).toNat=0 by decide,
    arguments,registers_paid,checkedRegs]

theorem finalStore_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (finalStore cfg s p ctx key value).host.registers=fun i=>if i=0 then some value else s.host.registers i := by
  unfold finalStore StateDispatchStorageTail.after StateDispatchStorageTail.cleaned
  rw [registers_finish,registers_cleanup]
  simpa only [StateDispatchStorageTail.returned,StateDispatchStorageTail.arguments,returned,arguments] using returned_registers cfg s p ctx key value

theorem callAfter_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (callAfter cfg s p ctx key value).host.registers=fun i=>if i=0 then some value else s.host.registers i := by
  unfold callAfter
  rw [finalStore_registers]
  simp only [entered,registers_charge]
end WNear.Proofs.StateDispatchStorage
