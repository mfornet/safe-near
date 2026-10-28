import Proofs.StateDecodeScalarGas

/-! Residual-credit cuts from the original scalar-reader store. Only the stated
ordinary-operation budget is required; all callee charges are already included. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] reserved guarded takeArguments taken wordArguments readWords accepted cached
  dropArguments dropped dropCached values updated restored after

theorem reserved_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest)) :
    (reserved s cfg.regularOpCost p).host.gas.Credits rest := by
  exact (reserved_gas wide cfg s p rest hc).2.2

theorem guarded_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (11*cfg.regularOpCost+rest)) :
    (guarded s cfg.regularOpCost p).host.gas.Credits rest := by
  exact (guarded_gas wide cfg s p rest hc).2.2

theorem takeArguments_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (19*cfg.regularOpCost+rest)) :
    (takeArguments s cfg.regularOpCost p).host.gas.Credits rest := by
  exact (takeArguments_gas wide cfg s p rest hc).2.2

theorem taken_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (41*cfg.regularOpCost+rest)) :
    (taken wide s cfg.regularOpCost p).host.gas.Credits rest := by
  exact (taken_gas wide cfg s p rest hc).2.2

theorem wordArguments_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (48*cfg.regularOpCost+rest)) :
    (wordArguments wide s cfg.regularOpCost p).host.gas.Credits rest := by
  exact (wordArguments_gas wide cfg s p rest hc).2.2

theorem readWords_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 82 else 74)*cfg.regularOpCost+rest)) :
    (readWords wide cfg s p).host.gas.Credits rest := by
  exact (readWords_gas wide cfg s p rest hc).2.2

theorem accepted_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 87 else 79)*cfg.regularOpCost+rest)) :
    (accepted wide cfg s p).host.gas.Credits rest := by
  exact (accepted_gas wide cfg s p rest hc).2.2

theorem cached_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 95 else 82)*cfg.regularOpCost+rest)) :
    (cached wide cfg s p).host.gas.Credits rest := by
  exact (cached_gas wide cfg s p rest hc).2.2

theorem dropArguments_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 102 else 91)*cfg.regularOpCost+rest)) :
    (dropArguments wide cfg s p).host.gas.Credits rest := by
  exact (dropArguments_gas wide cfg s p rest hc).2.2

theorem dropped_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 128 else 117)*cfg.regularOpCost+rest)) :
    (dropped wide cfg s p).host.gas.Credits rest := by
  exact (dropped_gas wide cfg s p rest hc).2.2

theorem dropCached_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 131 else 120)*cfg.regularOpCost+rest)) :
    (dropCached wide cfg s p).host.gas.Credits rest := by
  exact (dropCached_gas wide cfg s p rest hc).2.2

theorem values_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 141 else 125)*cfg.regularOpCost+rest)) :
    (values wide cfg s p).host.gas.Credits rest := by
  exact (values_gas wide cfg s p rest hc).2.2

theorem updated_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 146 else 130)*cfg.regularOpCost+rest)) :
    (updated wide cfg s p).host.gas.Credits rest := by
  exact (updated_gas wide cfg s p rest hc).2.2

theorem restored_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((if wide then 153 else 137)*cfg.regularOpCost+rest)) :
    (restored wide cfg s p).host.gas.Credits rest := by
  exact (restored_gas wide cfg s p rest hc).2.2

theorem after_credits (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost wide*cfg.regularOpCost+rest)) :
    (after wide cfg s p).host.gas.Credits rest := by
  have budget : s.host.gas.Credits ((if wide then 154 else 138)*cfg.regularOpCost+rest) := hc
  exact (after_gas wide cfg s p rest budget).2.2

end WNear.Proofs.StateDecodeScalar
