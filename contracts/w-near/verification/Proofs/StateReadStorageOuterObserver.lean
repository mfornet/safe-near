import Proofs.StateReadStorageOuterAccounting

/-! Exact used_gas observer state after459. The metered host updates this observer
at pre-invocation payment; later trie/post-call charges and guest cleanup are retained
in burnt gas without falsely replacing the observer by final burnt gas. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open Wasm Wasm.Near MeteredLogic

theorem result_usedGas (before : HostStore NearState) (len ptr reg : UInt64)
    (initial : _root_.Near.TrieOverlay.State) (p : ReadPlan) (value : List UInt8) :
    (result before len ptr reg initial p value).host.context.usedGas=UInt64.ofNat (prePaid before len ptr reg).gas.used := by
  let phase := p.result (beforeTrie before len ptr reg) initial
  let raw := written phase reg value
  have post := congrArg (fun h : NearState=>h.context.usedGas)
    (applyCharges_frame raw.host (writeReg value.length) (writeReg_burnsOnly value.length))
  change (applyCharges raw.host (writeReg value.length)).1.context.usedGas=_
  change (applyCharges raw.host (writeReg value.length)).1.context.usedGas=raw.host.context.usedGas at post
  rw [post]
  unfold raw written
  split <;> rfl
end Wasm.Near.MeteredHosts.StorageRead

namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] checked arguments returned finalStore callAfter

def hostBefore (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StorageReadCalls.beforeCall cfg (paid (StateReadStorage.entered (arguments s cfg.regularOpCost p) cfg.regularOpCost) cfg.regularOpCost 3) p.mi
private theorem usedGas_mask (before actual : NearState)
    (h : {actual with gas:=before.gas,gasProfile:=before.gasProfile}=before) : actual.context.usedGas=before.context.usedGas := by
  have eq := congrArg (fun h : NearState=>h.context.usedGas) h
  exact eq
private theorem observer_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.context.usedGas=s.host.context.usedGas := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem observer_charge (s : Store NearState) (n : Nat) : (chargedStore s n).host.context.usedGas=s.host.context.usedGas := rfl
private theorem observer_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).host.context.usedGas=s.host.context.usedGas := rfl
private theorem observer_finish (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (StateDispatchStorageFinish.after s op index sp).host.context.usedGas=s.host.context.usedGas := by
  simp only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.afterReturn,StateDispatchLengthFinish.afterReturn,
    StateDispatchStorageFinish.returned,StateDispatchReturn.callAfter,StateDispatchReturn.entered,StateDispatchReturn.after,
    StateDispatchReturn.suffixAfter,StateDispatchReturn.reserved,observer_paid,observer_global,observer_charge]
private theorem observer_cleanup (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (StateDispatchStorageCleanup.after s op index counter memory).host.context.usedGas=s.host.context.usedGas :=
  usedGas_mask s.host _ (StateDispatchStorageCleanup.after_host s op index counter memory)

theorem returned_usedGas (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (returned cfg s p ctx key value).host.context.usedGas=
      UInt64.ofNat (MeteredHosts.StorageRead.prePaid (hostBefore cfg s p) (keyLen p) (keyPtr p) 0).gas.used := by
  simp only [returned,StateReadStorage.callAfter,StateReadStorage.after,StorageReadCalls.callStore,commitHost_host,
    StorageReadCalls.after,MeteredHosts.StorageRead.result_usedGas,hostBefore]

theorem callAfter_usedGas (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (callAfter cfg s p ctx key value).host.context.usedGas=
      UInt64.ofNat (MeteredHosts.StorageRead.prePaid (hostBefore cfg (entered s cfg.regularOpCost) p) (keyLen p) (keyPtr p) 0).gas.used := by
  unfold callAfter finalStore StateDispatchStorageTail.after StateDispatchStorageTail.cleaned
  rw [observer_finish,observer_cleanup]
  simpa only [StateDispatchStorageTail.returned,StateDispatchStorageTail.arguments,returned,arguments] using
    returned_usedGas cfg (entered s cfg.regularOpCost) p ctx key value
end WNear.Proofs.StateDispatchStorage
