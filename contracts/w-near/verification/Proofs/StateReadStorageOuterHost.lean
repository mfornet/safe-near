import Proofs.StateReadStorageOuterState
import Proofs.StateReadStorageOuterCosts

/-! Original548 setup preserves prices/registers; the actual459 call writes
register zero and preserves the original price table. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] storageArguments setupStore highStore reserved stored
private theorem costs_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.extCosts=s.host.extCosts := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem costs_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).host.extCosts=s.host.extCosts := rfl
private theorem costs_store (s : Store NearState) (i a : Nat) (memory : Memory) (value : UInt32) : (storeI32 s i a memory value).host.extCosts=s.host.extCosts := rfl
private theorem regs_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.registers=s.host.registers := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem regs_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).host.registers=s.host.registers := rfl
private theorem regs_store (s : Store NearState) (i a : Nat) (memory : Memory) (value : UInt32) : (storeI32 s i a memory value).host.registers=s.host.registers := rfl

theorem stored_costs (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :
    (stored cfg s p ctx key).host.extCosts=s.host.extCosts := by
  rw [stored,StateDispatchStorage.callAfter_costs,storageArguments,costs_paid,setupStore,costs_store,costs_paid,
    highStore,costs_store,costs_paid,reserved,costs_global,costs_paid]

theorem stored_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :
    (stored cfg s p ctx key).host.registers=fun i=>if i=0 then some p.bytes else s.host.registers i := by
  rw [stored,StateDispatchStorage.callAfter_registers,storageArguments,regs_paid,setupStore,regs_store,regs_paid,
    highStore,regs_store,regs_paid,reserved,regs_global,regs_paid]

theorem stored_register_zero (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :
    (stored cfg s p ctx key).host.registers 0=some p.bytes := by
  rw [stored_registers]
  simp only [ite_true]
end WNear.Proofs.StateReadStorageOuter
