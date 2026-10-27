import Proofs.StateDispatchReadHost
import Proofs.StateReadRegisterHost

/-! The copy dispatcher reads the original register file and retains it. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] checked arguments returned
set_option maxRecDepth 16384

private theorem registers_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.registers = s.host.registers := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem arguments_registers (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).host.registers = s.host.registers := by
  have h := congrArg NearState.registers (checked_host s op p)
  simp only at h
  rw [arguments,registers_paid]
  exact h

theorem returned_registers (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    (returned cfg s p bytes).host.registers = s.host.registers := by
  unfold returned
  exact (StateReadRegister.readCallAfter_registers cfg (arguments s cfg.regularOpCost p) p.mi (ptr p) bytes).trans
    (arguments_registers s cfg.regularOpCost p)

end WNear.Proofs.StateDispatchRead
