import Proofs.StateReadStorageOuterKey
import Proofs.StateReadStorageOuterSetupFrame

/-! Canonical storage-read resources are assumed only on the original host and
memory. The actual setup and borrow key read is derived from their byte frame. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    view seed (storeI32 s index address memory value).host=view seed s.host := rfl
private theorem view_global (seed : NearState) (s : Store NearState) (index : Nat) (value : Value) :
    view seed (setGlobal s index value).host=view seed s.host := rfl

theorem storageArguments_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(storageArguments s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (storageArguments s op p).host=s.host
  simp only [storageArguments,setupStore,highStore,reserved,view_paid,view_store,view_global]
  rfl

theorem original_to_lowReady (p : Layout) (hn : Native p) (host : NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8)) (key : List UInt8)
    (hr : StorageReadCalls.Ready ⟨p.memory,host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes) :
    StorageReadCalls.Ready ⟨StateDispatchStorage.lowMemory (storageLayout p),host⟩ ctx raw storage
      (StateDispatchStorage.keyLen (storageLayout p)) (StateDispatchStorage.keyPtr (storageLayout p)) 0 key p.bytes := by
  exact ⟨hr.wf,hr.raw_eq,hr.represents,hr.nodes,hr.accounting,key_read p hn host key hr.key_read,
    hr.key_limit,hr.value_read,hr.register_limit,hr.proof⟩

theorem storage_host_ready (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8)) (key : List UInt8)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes) :
    StorageReadCalls.Ready ⟨StateDispatchStorage.lowMemory (storageLayout p),(storageArguments s cfg.regularOpCost p).host⟩
      ctx raw storage (StateDispatchStorage.keyLen (storageLayout p)) (StateDispatchStorage.keyPtr (storageLayout p)) 0 key p.bytes := by
  have low := original_to_lowReady p hn s.host ctx raw storage key hr
  exact StateDispatchStorage.ready_of_host_mask s.host (storageArguments s cfg.regularOpCost p).host
    (StateDispatchStorage.lowMemory (storageLayout p)) ctx raw storage _ _ 0 key p.bytes
    (storageArguments_functional_host s cfg.regularOpCost p) low
end WNear.Proofs.StateReadStorageOuter
