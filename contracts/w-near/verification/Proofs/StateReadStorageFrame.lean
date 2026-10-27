import Proofs.StateReadStorageCall

/-! Exact guest-memory/register frames and gas for the actual f284 hit call. -/
namespace WNear.Proofs.StateReadStorage
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits paid_gas)

 theorem after_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (after cfg s mi initial keyLen keyPtr register key value).mems[index]? = some memory :=
  StorageReadCalls.callStore_memory cfg (paid s cfg.regularOpCost 3) mi initial keyLen keyPtr register key value index memory hi hm

 theorem after_registers (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    (after cfg s mi initial keyLen keyPtr register key value).host.registers =
      if register = u64Max then s.host.registers else fun i => if i = register.toNat then some value else s.host.registers i :=
  StorageReadCalls.callStore_registers cfg (paid s cfg.regularOpCost 3) mi initial keyLen keyPtr register key value

 theorem after_fields (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    (after cfg s mi initial keyLen keyPtr register key value).funcs = s.funcs ∧
    (after cfg s mi initial keyLen keyPtr register key value).modules = s.modules ∧
    (after cfg s mi initial keyLen keyPtr register key value).tables = s.tables ∧
    (after cfg s mi initial keyLen keyPtr register key value).globals = s.globals :=
  StorageReadCalls.callStore_fields cfg (paid s cfg.regularOpCost 3) mi initial keyLen keyPtr register key value

 theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (callAfter cfg s mi initial keyLen keyPtr register key value).mems[index]? = some memory :=
  after_memory cfg (entered s cfg.regularOpCost) mi initial keyLen keyPtr register key value index memory hi hm

 theorem callAfter_registers (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    (callAfter cfg s mi initial keyLen keyPtr register key value).host.registers =
      if register = u64Max then s.host.registers else fun i => if i = register.toNat then some value else s.host.registers i :=
  after_registers cfg (entered s cfg.regularOpCost) mi initial keyLen keyPtr register key value

 theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (initial : _root_.Near.TrieOverlay.State)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) :
    (callAfter cfg s mi initial keyLen keyPtr register key value).funcs = s.funcs ∧
    (callAfter cfg s mi initial keyLen keyPtr register key value).modules = s.modules ∧
    (callAfter cfg s mi initial keyLen keyPtr register key value).tables = s.tables ∧
    (callAfter cfg s mi initial keyLen keyPtr register key value).globals = s.globals :=
  after_fields cfg (entered s cfg.regularOpCost) mi initial keyLen keyPtr register key value

 theorem after_gas (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest)) :
    (after cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.burnt = s.host.gas.burnt +
      4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value ∧
    (after cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.promises = s.host.gas.promises ∧
    (after cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let fee := StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value
  have cp : (paid s op 3).host.gas.Credits (op + (fee + rest)) := paid_credits s op 3 _ (hc.mono (by dsimp [op,fee]; omega))
  have ch : (paid s op 3).host.gas.Credits (cfg.regularOpCost + (StorageReadCalls.cost ⟨memory,(paid s op 3).host⟩ ctx.trie keyLen keyPtr register key value + rest)) := by
    rw [cost_paid]; exact cp
  have hg := paid_gas s op 3 (op + (fee + rest)) (hc.mono (by dsimp [op,fee]; omega))
  have h := StorageReadCalls.callStore_gas cfg (paid s op 3) mi index memory ctx raw storage keyLen keyPtr register key value rest hi hm
    (ready_paid s op 3 memory ctx raw storage keyLen keyPtr register key value hr) ch
  rw [cost_paid] at h
  refine ⟨?_,h.2.1.trans hg.2,h.2.2⟩
  change (StorageReadCalls.callStore cfg (paid s op 3) mi ctx.trie keyLen keyPtr register key value).host.gas.burnt = _
  rw [h.1,hg.1]
  dsimp [op]; omega

 theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (rest : Nat)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest)) :
    (callAfter cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.burnt = s.host.gas.burnt +
      17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value ∧
    (callAfter cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.promises = s.host.gas.promises ∧
    (callAfter cfg s mi ctx.trie keyLen keyPtr register key value).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let fee := StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value
  have h0 := GasCounter.burn_credits s.host.gas op (12 * op + (4 * op + fee + rest)) (hc.mono (by dsimp [op,fee]; omega))
  have h1 := GasCounter.burn_credits (chargedStore s op).host.gas (12 * op) (4 * op + fee + rest) h0.2.2.2
  have ce : StorageReadCalls.cost ⟨memory,(entered s op).host⟩ ctx.trie keyLen keyPtr register key value = fee := cost_entered s op memory ctx.trie keyLen keyPtr register key value
  have ca : (entered s op).host.gas.Credits (4 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,(entered s op).host⟩ ctx.trie keyLen keyPtr register key value + rest) := by
    rw [ce]; exact h1.2.2.2
  have h := after_gas cfg (entered s op) mi index memory ctx raw storage keyLen keyPtr register key value rest hi hm
    (ready_entered s op memory ctx raw storage keyLen keyPtr register key value hr) ca
  rw [ce] at h
  refine ⟨?_,h.2.1.trans (h1.2.2.1.trans h0.2.2.1),h.2.2⟩
  rw [callAfter,h.1]
  have b0 : (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op := h0.2.1
  have b1 : (entered s op).host.gas.burnt = (chargedStore s op).host.gas.burnt + 12 * op := h1.2.1
  rw [b1,b0]
  dsimp [op,fee]; omega
end WNear.Proofs.StateReadStorage
