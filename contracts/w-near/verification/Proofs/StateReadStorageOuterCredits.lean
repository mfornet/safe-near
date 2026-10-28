import Proofs.StateReadStorageOuterHost
import Proofs.StateReadStorageOuterPhases
import Proofs.StateReadStorageOuterHostReady

/-! Residual credits for the actual548 canonical-hit call sequence. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] stored guarded registerArguments registered optionArguments converted after actualRegister fee

private theorem storage_call_credits (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchStorage.Layout)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key value : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨StateDispatchStorage.lowMemory p,s.host⟩ ctx raw storage
      (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value)
    (hc : s.host.gas.Credits (261*cfg.regularOpCost+StateDispatchStorage.fee s p ctx key value+rest)) :
    (StateDispatchStorage.callAfter cfg s p ctx key value).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let active := StateDispatchStorage.entered s op
  have c0 := StorePair.charged_credits s op (12*op+(248*op+StateDispatchStorage.fee s p ctx key value+rest))
    (hc.mono (by dsimp [op];omega))
  have ca := StorePair.charged_credits (chargedStore s op) (12*op) (248*op+StateDispatchStorage.fee s p ctx key value+rest) c0
  have ra : StorageReadCalls.Ready ⟨StateDispatchStorage.lowMemory p,active.host⟩ ctx raw storage
      (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value :=
    (hr.charge _ op ctx raw storage _ _ _ key value).charge _ (12*op) ctx raw storage _ _ _ key value
  have feeEq : StateDispatchStorage.fee active p ctx key value=StateDispatchStorage.fee s p ctx key value := by
    exact StateReadStorage.cost_entered s op (StateDispatchStorage.lowMemory p) ctx.trie _ _ _ key value
  have cb : active.host.gas.Credits (248*cfg.regularOpCost+StateDispatchStorage.fee active p ctx key value+rest) := by
    rw [feeEq];exact ca
  unfold StateDispatchStorage.callAfter
  exact StateDispatchStorage.final_credits cfg active p ctx raw storage key value rest hi hm ra cb

theorem stored_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc : s.host.gas.Credits (276*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest)) :
    (stored cfg s p ctx key).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let args := storageArguments s op p
  have ca := storageArguments_credits s op (261*op+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest) p
    (hc.mono (by dsimp [op];omega))
  have feeEq : StateDispatchStorage.fee args (storageLayout p) ctx key p.bytes=
      StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes :=
    StateDispatchStorage.cost_of_host_mask s.host args.host _ ctx.trie _ _ _ key p.bytes (storageArguments_functional_host s op p)
  have cb : args.host.gas.Credits (261*cfg.regularOpCost+StateDispatchStorage.fee args (storageLayout p) ctx key p.bytes+rest) := by
    rw [feeEq];exact ca
  unfold stored
  exact storage_call_credits cfg args (storageLayout p) ctx raw storage key p.bytes rest hi
    (storageArguments_memory s op p hm) (storage_host_ready cfg s p hn ctx raw storage key hr) cb

private theorem costs_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.extCosts=s.host.extCosts := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem registerArguments_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :
    (registerArguments cfg s p ctx key).host.extCosts=s.host.extCosts := by
  rw [registerArguments,costs_paid,guarded,costs_paid,stored_costs]

theorem guarded_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc : s.host.gas.Credits (283*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest)) :
    (guarded cfg s p ctx key).host.gas.Credits rest := by
  unfold guarded
  exact paid_credits (stored cfg s p ctx key) cfg.regularOpCost 7 rest
    (stored_credits cfg s p hn ctx raw storage key _ hi hm hr (hc.mono (by omega)))

theorem registerArguments_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc : s.host.gas.Credits (287*cfg.regularOpCost+StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+rest)) :
    (registerArguments cfg s p ctx key).host.gas.Credits rest := by
  unfold registerArguments
  exact paid_credits (guarded cfg s p ctx key) cfg.regularOpCost 4 rest
    (guarded_credits cfg s p hn ctx raw storage key _ hi hm hr (hc.mono (by omega)))

theorem registered_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc : s.host.gas.Credits ((StateReadRegisterOuter.bodyCost (actualRegister p)+298)*cfg.regularOpCost+fee cfg s p ctx key+rest)) :
    (registered cfg s p ctx key).host.gas.Credits rest := by
  have ca := registerArguments_credits cfg s p hn ctx raw storage key
    ((StateReadRegisterOuter.bodyCost (actualRegister p)+11)*cfg.regularOpCost+StateReadRegisterOuter.fee cfg s (actualRegister p)+rest)
    hi hm hr (hc.mono (by simp only [fee,Nat.add_mul];omega))
  have feeEq : StateReadRegisterOuter.fee cfg (registerArguments cfg s p ctx key) (actualRegister p)=
      StateReadRegisterOuter.fee cfg s (actualRegister p) := by
    simp only [StateReadRegisterOuter.fee,RegisterRead.readCost,registerArguments_costs]
  have cb : (registerArguments cfg s p ctx key).host.gas.Credits
      ((StateReadRegisterOuter.bodyCost (actualRegister p)+11)*cfg.regularOpCost+
       StateReadRegisterOuter.fee cfg (registerArguments cfg s p ctx key) (actualRegister p)+rest) := by
    rw [feeEq];exact ca
  unfold registered
  exact StateReadRegisterOuter.callAfter_credits cfg (registerArguments cfg s p ctx key) (actualRegister p) rest cb

theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key : List UInt8) (rest : Nat)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hr : StorageReadCalls.Ready ⟨p.memory,s.host⟩ ctx raw storage
      (UInt64.ofNat p.keyLen.toNat) (UInt64.ofNat p.keyPtr.toNat) 0 key p.bytes)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg s p ctx key+rest)) :
    (after cfg s p ctx key).host.gas.Credits rest := by
  have cr := registered_credits cfg s p hn ctx raw storage key (38*cfg.regularOpCost+rest) hi hm hr
    (hc.mono (by simp only [bodyCost,Nat.add_mul];omega))
  have ca := paid_credits (registered cfg s p ctx key) cfg.regularOpCost 7 (27*cfg.regularOpCost+(4*cfg.regularOpCost+rest))
    (cr.mono (by omega))
  have cd := StateReadResult.callAfter_credits (optionArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex
    (4*cfg.regularOpCost+rest) (registeredMemory p) p.out548 (scratch p+16) (by simpa only [optionArguments] using ca)
  unfold after
  exact paid_credits (converted cfg s p ctx key) cfg.regularOpCost 4 rest (by simpa only [converted] using cd)
end WNear.Proofs.StateReadStorageOuter
