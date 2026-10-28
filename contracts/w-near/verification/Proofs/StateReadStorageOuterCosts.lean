import Proofs.StateReadStorageOuterRegisters

/-! Actual canonical storage-read billing frames its price table, while the
completed read retains the precise fetched trie accounting state. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

theorem result_extCosts (before : HostStore NearState) (len ptr reg : UInt64)
    (initial : _root_.Near.TrieOverlay.State) (p : ReadPlan) (value : List UInt8) :
    (result before len ptr reg initial p value).host.extCosts=before.host.extCosts := by
  let phase := p.result (beforeTrie before len ptr reg) initial
  let raw := written phase reg value
  have pre := congrArg NearState.extCosts (applyCharges_frame before.host (preCharges before len ptr reg)
    (beforeCharges_burnsOnly before len ptr reg))
  have post := congrArg NearState.extCosts (applyCharges_frame raw.host (writeReg value.length) (writeReg_burnsOnly value.length))
  change (applyCharges raw.host (writeReg value.length)).1.extCosts=_
  change (applyCharges raw.host (writeReg value.length)).1.extCosts=raw.host.extCosts at post
  rw [post]
  change (prePaid before len ptr reg).extCosts=before.host.extCosts at pre
  unfold raw written
  split <;> simpa only [phase,ReadPlan.result,StorageMetered.prepared,beforeTrie,Output.paidStore,NearState.setRegister] using pre

theorem result_accounting (before : HostStore NearState) (len ptr reg : UInt64)
    (initial : _root_.Near.TrieOverlay.State) (p : ReadPlan) (value : List UInt8) :
    (result before len ptr reg initial p value).host.storageAccounting=some p.fetched := by
  let phase := p.result (beforeTrie before len ptr reg) initial
  let raw := written phase reg value
  have post := congrArg NearState.storageAccounting (applyCharges_frame raw.host (writeReg value.length) (writeReg_burnsOnly value.length))
  change (applyCharges raw.host (writeReg value.length)).1.storageAccounting=_
  change (applyCharges raw.host (writeReg value.length)).1.storageAccounting=raw.host.storageAccounting at post
  rw [post]
  unfold raw written
  split <;> rfl
end Wasm.Near.MeteredHosts.StorageRead

namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] checked arguments returned finalStore callAfter

private theorem costs_of_mask (before actual : NearState)
    (h : {actual with gas:=before.gas,gasProfile:=before.gasProfile}=before) : actual.extCosts=before.extCosts := by
  have eq := congrArg NearState.extCosts h
  exact eq
private theorem costs_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.extCosts=s.host.extCosts := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem costs_charge (s : Store NearState) (n : Nat) : (chargedStore s n).host.extCosts=s.host.extCosts := rfl
private theorem costs_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).host.extCosts=s.host.extCosts := rfl
private theorem costs_finish (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (StateDispatchStorageFinish.after s op index sp).host.extCosts=s.host.extCosts := by
  simp only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.afterReturn,StateDispatchLengthFinish.afterReturn,
    StateDispatchStorageFinish.returned,StateDispatchReturn.callAfter,StateDispatchReturn.entered,StateDispatchReturn.after,
    StateDispatchReturn.suffixAfter,StateDispatchReturn.reserved,costs_paid,costs_global,costs_charge]
private theorem costs_cleanup (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (StateDispatchStorageCleanup.after s op index counter memory).host.extCosts=s.host.extCosts :=
  costs_of_mask s.host _ (StateDispatchStorageCleanup.after_host s op index counter memory)

private theorem storage_costs (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (initial : _root_.Near.TrieOverlay.State) (len ptr reg : UInt64) (key value : List UInt8) :
    (StateReadStorage.callAfter cfg s mi initial len ptr reg key value).host.extCosts=s.host.extCosts := by
  simp only [StateReadStorage.callAfter,StateReadStorage.after,StorageReadCalls.callStore,commitHost_host,
    StorageReadCalls.after,MeteredHosts.StorageRead.result_extCosts,StorageReadCalls.beforeCall,StateReadStorage.entered,costs_charge,costs_paid]

theorem returned_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (returned cfg s p ctx key value).host.extCosts=s.host.extCosts := by
  have checkedCosts := costs_of_mask s.host _ (checked_host s cfg.regularOpCost p)
  rw [returned,storage_costs,arguments,costs_paid,checkedCosts]

theorem callAfter_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (callAfter cfg s p ctx key value).host.extCosts=s.host.extCosts := by
  unfold callAfter finalStore StateDispatchStorageTail.after StateDispatchStorageTail.cleaned
  rw [costs_finish,costs_cleanup]
  have tail := returned_costs cfg (entered s cfg.regularOpCost) p ctx key value
  simpa only [StateDispatchStorageTail.returned,StateDispatchStorageTail.arguments,returned,arguments,entered,costs_charge] using tail
end WNear.Proofs.StateDispatchStorage
