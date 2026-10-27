import Proofs.StateReadRegisterFrame

/-! Register-copy host calls retain the register file while updating gas context. -/
namespace WNear.Proofs.StateReadRegister
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)

private theorem paid_registers (s : Store NearState) (op n : Nat) : (paid s op n).host.registers = s.host.registers := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem readStore_registers (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    (RegisterCalls.readStore cfg s mi ptr bytes).host.registers = s.host.registers := by
  have h := congrArg NearState.registers (applyCharges_frame (RegisterCalls.beforeCall cfg s mi).host
    (RegisterRead.readCharges bytes.length) (RegisterRead.readCharges_burns bytes.length))
  simp only at h
  simpa only [RegisterCalls.readStore,commitHost_host,RegisterCalls.readAfter,RegisterRead.paid,
    Output.paidStore,RegisterCalls.beforeCall,chargedStore,chargeHost] using h

theorem readCallAfter_registers (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    (readCallAfter cfg s mi ptr bytes).host.registers = s.host.registers := by
  rw [readCallAfter,readAfter,readStore_registers,paid_registers]
  rfl

end WNear.Proofs.StateReadRegister
