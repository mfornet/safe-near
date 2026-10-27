import NearVM.MeteredStorageReadRules

/-! Exact gas and immutable guest resources across the actual storage-read opcode. -/
namespace Wasm.Near.MeteredLogic.StorageReadCalls
open MeteredHosts
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

theorem beforeCall_memory (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (hi : mi.memAddrs[0]? = some index) (hm : store.mems[index]? = some memory) :
    (beforeCall cfg store mi).mem = memory := by
  simp [beforeCall, Store.memOf, hi, hm]

/-- Opcode burn, complete actual host charges, and residual credit. -/
theorem callStore_gas (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (hi : mi.memAddrs[0]? = some memoryIndex) (hm : store.mems[memoryIndex]? = some memory)
    (ready : Ready ⟨memory,store.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : store.host.gas.Credits (cfg.regularOpCost + (cost ⟨memory,store.host⟩ ctx.trie keyLen keyPtr register key value + rest))) :
    (callStore cfg store mi ctx.trie keyLen keyPtr register key value).host.gas.burnt =
      store.host.gas.burnt + cfg.regularOpCost + cost ⟨memory,store.host⟩ ctx.trie keyLen keyPtr register key value ∧
    (callStore cfg store mi ctx.trie keyLen keyPtr register key value).host.gas.promises = store.host.gas.promises ∧
    (callStore cfg store mi ctx.trie keyLen keyPtr register key value).host.gas.Credits rest := by
  let original : HostStore NearState := ⟨memory,store.host⟩
  let fee := cost original ctx.trie keyLen keyPtr register key value
  have mem := beforeCall_memory cfg store mi memoryIndex memory hi hm
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost (fee + rest) hc
  have hbefore : beforeCall cfg store mi = {original with host := (chargeHost store.host cfg.regularOpCost).1} :=
    congrArg (fun m => (⟨m,(chargedStore store cfg.regularOpCost).host⟩ : HostStore NearState)) mem
  have hr : Ready (beforeCall cfg store mi) ctx raw storage keyLen keyPtr register key value := by
    rw [hbefore]
    exact ready.charge original cfg.regularOpCost ctx raw storage keyLen keyPtr register key value
  have hcost : cost (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value = fee := by rw [hbefore, cost_charge]
  have cc : (beforeCall cfg store mi).host.gas.Credits
      (burnSum (beforeCall cfg store mi).host.extCosts (StorageRead.preCharges (beforeCall cfg store mi) keyLen keyPtr register) +
      (burnSum (beforeCall cfg store mi).host.extCosts
        ((StorageRead.readPlan ctx.trie (contractKey (beforeCall cfg store mi).host.context.currentAccountId key)
          (beforeCall cfg store mi).host.storageReadsFromTrie).charges ctx.trie) +
      (burnSum (beforeCall cfg store mi).host.extCosts (writeReg value.length) + rest))) := by
    have hh : (beforeCall cfg store mi).host.gas.Credits (cost (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value + rest) := by
      rw [hcost]; exact hb.2.2.2
    simpa only [cost, Nat.add_assoc] using hh
  have h := StorageRead.canonical_contract 0 (beforeCall cfg store mi) ctx raw hr.wf storage hr.raw_eq hr.represents hr.nodes
    keyLen keyPtr register key value rest hr.accounting hr.key_read hr.key_limit hr.value_read hr.register_limit hr.proof cc
  have burn : (after (beforeCall cfg store mi) ctx.trie keyLen keyPtr register key value).host.gas.burnt =
      (beforeCall cfg store mi).host.gas.burnt + fee := by
    rw [← hcost]
    simpa only [after, cost, Nat.add_assoc] using h.2.1
  have opcode : (beforeCall cfg store mi).host.gas.burnt = store.host.gas.burnt + cfg.regularOpCost := hb.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [callStore, commitHost_host]
    rw [burn, opcode]
  · simp only [callStore, commitHost_host]
    exact h.2.2.1.trans hb.2.2.1
  · simpa only [callStore, commitHost_host, after] using h.2.2.2

theorem callStore_credits (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (storage : List (List UInt8 × List UInt8)) (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (hi : mi.memAddrs[0]? = some memoryIndex) (hm : store.mems[memoryIndex]? = some memory)
    (ready : Ready ⟨memory,store.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : store.host.gas.Credits (cfg.regularOpCost + (cost ⟨memory,store.host⟩ ctx.trie keyLen keyPtr register key value + rest))) :
    (callStore cfg store mi ctx.trie keyLen keyPtr register key value).host.gas.Credits rest :=
  (callStore_gas cfg store mi memoryIndex memory ctx raw storage keyLen keyPtr register key value rest hi hm ready hc).2.2

/-- Committing the unchanged host memory retains all code and global arrays. -/
theorem callStore_fields (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    (callStore cfg store mi initial keyLen keyPtr register key value).funcs = store.funcs ∧
    (callStore cfg store mi initial keyLen keyPtr register key value).modules = store.modules ∧
    (callStore cfg store mi initial keyLen keyPtr register key value).tables = store.tables ∧
    (callStore cfg store mi initial keyLen keyPtr register key value).globals = store.globals := by
  simp only [callStore, Exec.commitHost, Store.setMemOf]
  cases mi.memAddrs[0]? <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem callStore_memory (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : store.mems[index]? = some memory) :
    (callStore cfg store mi initial keyLen keyPtr register key value).mems[index]? = some memory := by
  have mem := beforeCall_memory cfg store mi index memory hi hm
  have hresult : (after (beforeCall cfg store mi) initial keyLen keyPtr register key value).mem = memory :=
    (StorageRead.result_memory _ _ _ _ _ _ _).trans mem
  have hb : index < store.mems.size := by
    by_contra h
    have hn : store.mems[index]? = none := Array.getElem?_eq_none (by omega)
    rw [hn] at hm
    cases hm
  simp only [callStore, Exec.commitHost, Store.setMemOf, hi, hresult, chargedStore,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hb]

theorem callStore_registers (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    (callStore cfg store mi initial keyLen keyPtr register key value).host.registers =
      if register = u64Max then store.host.registers else
        fun i => if i = register.toNat then some value else store.host.registers i := by
  simp only [callStore, commitHost_host, after]
  exact StorageRead.result_registers _ _ _ _ _ _ _

theorem callStore_register (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (hr : register ≠ u64Max) :
    (callStore cfg store mi initial keyLen keyPtr register key value).host.registers register.toNat = some value := by
  rw [callStore_registers]
  simp [hr]

theorem callStore_other_register (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (initial : State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (index : Nat) (h : index ≠ register.toNat) :
    (callStore cfg store mi initial keyLen keyPtr register key value).host.registers index = store.host.registers index := by
  rw [callStore_registers]
  by_cases hd : register = u64Max <;> simp [hd, h]

end Wasm.Near.MeteredLogic.StorageReadCalls
