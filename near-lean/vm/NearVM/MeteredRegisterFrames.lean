import NearVM.MeteredRegisterRules

/-! Resource transport and exact gas for committed register host calls. -/
namespace Wasm.Near.MeteredLogic.RegisterCalls
open MeteredHosts

theorem lengthStore_fields (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) :
    (lengthStore cfg store mi).funcs = store.funcs ∧
    (lengthStore cfg store mi).modules = store.modules ∧
    (lengthStore cfg store mi).tables = store.tables ∧
    (lengthStore cfg store mi).globals = store.globals := by
  simp only [lengthStore, Exec.commitHost, Store.setMemOf, chargedStore]
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem readStore_fields (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    (readStore cfg store mi ptr bytes).funcs = store.funcs ∧
    (readStore cfg store mi ptr bytes).modules = store.modules ∧
    (readStore cfg store mi ptr bytes).tables = store.tables ∧
    (readStore cfg store mi ptr bytes).globals = store.globals := by
  simp only [readStore, Exec.commitHost, Store.setMemOf, chargedStore]
  split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem lengthValue_beforeCall (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (register : UInt64) :
    RegisterRead.lengthValue (beforeCall cfg store mi) register =
      RegisterRead.lengthValue ⟨(store.memOf mi).getD (Memory.new 0 none), store.host⟩ register := rfl

/-- The caller opcode and host charge are both derived from the original credit offer. -/
theorem lengthStore_credits (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (rest : Nat)
    (hc : store.host.gas.Credits (cfg.regularOpCost + (store.host.extCosts.cost "base" + rest))) :
    (lengthStore cfg store mi).host.gas.burnt =
      store.host.gas.burnt + cfg.regularOpCost + store.host.extCosts.cost "base" ∧
    (lengthStore cfg store mi).host.gas.promises = store.host.gas.promises ∧
    (lengthStore cfg store mi).host.gas.Credits rest := by
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost
    (store.host.extCosts.cost "base" + rest) hc
  have hh : (beforeCall cfg store mi).host.gas.Credits
      (burnSum (beforeCall cfg store mi).host.extCosts [.ext "base"] + rest) := by
    rw [RegisterRead.length_cost]
    exact hb.2.2.2
  have hp := RegisterRead.paid_credits (beforeCall cfg store mi) [.ext "base"] rest
    (by simp [BurnsOnly]) hh
  have hext : (beforeCall cfg store mi).host.extCosts = store.host.extCosts := rfl
  have hburn : (beforeCall cfg store mi).host.gas.burnt = store.host.gas.burnt + cfg.regularOpCost := hb.2.1
  have hg := hp.2.1
  simp only [RegisterRead.length_cost, hext, hburn] at hg
  simp only [lengthStore, commitHost_host, lengthAfter]
  refine ⟨?_, hp.2.2.1.trans hb.2.2.1, hp.2.2.2⟩
  exact hg

theorem readStore_credits (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) (rest : Nat)
    (hc : store.host.gas.Credits (cfg.regularOpCost + (RegisterRead.readCost store.host bytes.length + rest))) :
    (readStore cfg store mi ptr bytes).host.gas.burnt =
      store.host.gas.burnt + cfg.regularOpCost + RegisterRead.readCost store.host bytes.length ∧
    (readStore cfg store mi ptr bytes).host.gas.promises = store.host.gas.promises ∧
    (readStore cfg store mi ptr bytes).host.gas.Credits rest := by
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost
    (RegisterRead.readCost store.host bytes.length + rest) hc
  have hh : (beforeCall cfg store mi).host.gas.Credits
      (burnSum (beforeCall cfg store mi).host.extCosts (RegisterRead.readCharges bytes.length) + rest) := by
    rw [RegisterRead.read_cost]
    exact hb.2.2.2
  have hp := RegisterRead.paid_credits (beforeCall cfg store mi) (RegisterRead.readCharges bytes.length) rest
    (RegisterRead.readCharges_burns _) hh
  have hcost : RegisterRead.readCost (beforeCall cfg store mi).host bytes.length =
      RegisterRead.readCost store.host bytes.length := rfl
  have hburn : (beforeCall cfg store mi).host.gas.burnt = store.host.gas.burnt + cfg.regularOpCost := hb.2.1
  have hg := hp.2.1
  simp only [RegisterRead.read_cost, hcost, hburn] at hg
  simp only [readStore, commitHost_host, readAfter]
  refine ⟨?_, hp.2.2.1.trans hb.2.2.1, hp.2.2.2⟩
  exact hg

end Wasm.Near.MeteredLogic.RegisterCalls
