import Proofs.StateReadStorageOuterHost

/-! The actual459 endpoint records the fetched trie state. This is deliberately
an update, rather than a false frame of the original storage accounting. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] checked arguments returned finalStore callAfter MeteredHosts.StorageRead.readPlan MeteredHosts.StorageCanonical.LookupPlan.fetched

private def header (h : NearState) := (h.context.currentAccountId,h.storageReadsFromTrie)
private theorem header_charge (s : Store NearState) (n : Nat) : header (chargedStore s n).host=header s.host := rfl
private theorem header_paid (s : Store NearState) (op n : Nat) : header (paid s op n).host=header s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem header_mask (before actual : NearState)
    (h : {actual with gas:=before.gas,gasProfile:=before.gasProfile}=before) : header actual=header before := by
  have eq := congrArg header h
  exact eq
private theorem accounting_mask (before actual : NearState)
    (h : {actual with gas:=before.gas,gasProfile:=before.gasProfile}=before) : actual.storageAccounting=before.storageAccounting := by
  have eq := congrArg NearState.storageAccounting h
  exact eq
private theorem accounting_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.storageAccounting=s.host.storageAccounting := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem accounting_charge (s : Store NearState) (n : Nat) : (chargedStore s n).host.storageAccounting=s.host.storageAccounting := rfl
private theorem accounting_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).host.storageAccounting=s.host.storageAccounting := rfl
private theorem accounting_finish (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (StateDispatchStorageFinish.after s op index sp).host.storageAccounting=s.host.storageAccounting := by
  simp only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.afterReturn,StateDispatchLengthFinish.afterReturn,
    StateDispatchStorageFinish.returned,StateDispatchReturn.callAfter,StateDispatchReturn.entered,StateDispatchReturn.after,
    StateDispatchReturn.suffixAfter,StateDispatchReturn.reserved,accounting_paid,accounting_global,accounting_charge]
private theorem accounting_cleanup (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (StateDispatchStorageCleanup.after s op index counter memory).host.storageAccounting=s.host.storageAccounting :=
  accounting_mask s.host _ (StateDispatchStorageCleanup.after_host s op index counter memory)

private theorem callStore_accounting (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (initial : _root_.Near.TrieOverlay.State) (len ptr reg : UInt64) (key value : List UInt8) :
    (StorageReadCalls.callStore cfg s mi initial len ptr reg key value).host.storageAccounting=
      some (MeteredHosts.StorageRead.readPlan initial (_root_.Near.TrieOverlay.contractKey s.host.context.currentAccountId key)
        s.host.storageReadsFromTrie).fetched := by
  have hb : header (StorageReadCalls.beforeCall cfg s mi).host=header s.host := rfl
  have account := congrArg Prod.fst hb
  have mode := congrArg Prod.snd hb
  change (StorageReadCalls.beforeCall cfg s mi).host.context.currentAccountId=s.host.context.currentAccountId at account
  change (StorageReadCalls.beforeCall cfg s mi).host.storageReadsFromTrie=s.host.storageReadsFromTrie at mode
  simp only [StorageReadCalls.callStore,commitHost_host,StorageReadCalls.after,MeteredHosts.StorageRead.result_accounting]
  rw [account,mode]

private theorem storage_accounting (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (initial : _root_.Near.TrieOverlay.State) (len ptr reg : UInt64) (key value : List UInt8) :
    (StateReadStorage.callAfter cfg s mi initial len ptr reg key value).host.storageAccounting=
      some (MeteredHosts.StorageRead.readPlan initial (_root_.Near.TrieOverlay.contractKey s.host.context.currentAccountId key)
        s.host.storageReadsFromTrie).fetched := by
  have hb : header (paid (StateReadStorage.entered s cfg.regularOpCost) cfg.regularOpCost 3).host=header s.host := by
    rw [header_paid,StateReadStorage.entered,header_charge,header_charge]
  have account := congrArg Prod.fst hb
  have mode := congrArg Prod.snd hb
  change (paid (StateReadStorage.entered s cfg.regularOpCost) cfg.regularOpCost 3).host.context.currentAccountId=s.host.context.currentAccountId at account
  change (paid (StateReadStorage.entered s cfg.regularOpCost) cfg.regularOpCost 3).host.storageReadsFromTrie=s.host.storageReadsFromTrie at mode
  rw [StateReadStorage.callAfter,StateReadStorage.after,callStore_accounting,account,mode]

theorem returned_accounting (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (returned cfg s p ctx key value).host.storageAccounting=
      some (MeteredHosts.StorageRead.readPlan ctx.trie (_root_.Near.TrieOverlay.contractKey s.host.context.currentAccountId key)
        s.host.storageReadsFromTrie).fetched := by
  have head := header_mask s.host _ (checked_host s cfg.regularOpCost p)
  have args : header (arguments s cfg.regularOpCost p).host=header s.host := by rw [arguments,header_paid];exact head
  have account := congrArg Prod.fst args
  have mode := congrArg Prod.snd args
  change (arguments s cfg.regularOpCost p).host.context.currentAccountId=s.host.context.currentAccountId at account
  change (arguments s cfg.regularOpCost p).host.storageReadsFromTrie=s.host.storageReadsFromTrie at mode
  rw [returned,storage_accounting,account,mode]

theorem callAfter_accounting (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8) :
    (callAfter cfg s p ctx key value).host.storageAccounting=
      some (MeteredHosts.StorageRead.readPlan ctx.trie (_root_.Near.TrieOverlay.contractKey s.host.context.currentAccountId key)
        s.host.storageReadsFromTrie).fetched := by
  unfold callAfter finalStore StateDispatchStorageTail.after StateDispatchStorageTail.cleaned
  rw [accounting_finish,accounting_cleanup]
  have tail := returned_accounting cfg (entered s cfg.regularOpCost) p ctx key value
  simpa only [StateDispatchStorageTail.returned,StateDispatchStorageTail.arguments,returned,arguments,entered,chargedStore,chargeHost] using tail
end WNear.Proofs.StateDispatchStorage

namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] stored storageArguments setupStore highStore reserved MeteredHosts.StorageRead.readPlan MeteredHosts.StorageCanonical.LookupPlan.fetched
private def header (h : NearState) := (h.context.currentAccountId,h.storageReadsFromTrie)
private theorem header_paid (s : Store NearState) (op n : Nat) : header (paid s op n).host=header s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem header_global (s : Store NearState) (i : Nat) (v : Value) : header (setGlobal s i v).host=header s.host := rfl
private theorem header_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : header (storeI32 s i a m v).host=header s.host := rfl

theorem stored_accounting (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (stored cfg s p ctx key).host.storageAccounting=
      some (MeteredHosts.StorageRead.readPlan ctx.trie (_root_.Near.TrieOverlay.contractKey s.host.context.currentAccountId key)
        s.host.storageReadsFromTrie).fetched := by
  have h : header (storageArguments s cfg.regularOpCost p).host=header s.host := by
    rw [storageArguments,header_paid,setupStore,header_store,header_paid,highStore,header_store,header_paid,reserved,header_global,header_paid]
  have account := congrArg Prod.fst h
  have mode := congrArg Prod.snd h
  change (storageArguments s cfg.regularOpCost p).host.context.currentAccountId=s.host.context.currentAccountId at account
  change (storageArguments s cfg.regularOpCost p).host.storageReadsFromTrie=s.host.storageReadsFromTrie at mode
  rw [stored,StateDispatchStorage.callAfter_accounting,account,mode]
end WNear.Proofs.StateReadStorageOuter
