import Proofs.ValueReturnDispatch

/-! Four-byte unsigned dispatch loads always denote ordinary memory lengths,
never the host's all-ones u64 register sentinel. -/
namespace WNear.Proofs.ValueReturnPacked
open Wasm Wasm.Near MeteredLogic

theorem packed32_bound (memory : Memory) (address : Nat) :
    (ValueReturnDispatch.packed32 memory address).toNat < 2 ^ 32 := by
  have h0 := (memory.read8 address).toNat_lt
  have h1 := (memory.read8 (address + 1)).toNat_lt
  have h2 := (memory.read8 (address + 2)).toNat_lt
  have h3 := (memory.read8 (address + 3)).toNat_lt
  simp [ValueReturnDispatch.packed32, List.range_succ]
  omega

theorem packed32_ne_sentinel (memory : Memory) (address : Nat) :
    ValueReturnDispatch.packed32 memory address ≠ u64Max := by
  have hb := packed32_bound memory address
  intro he
  rw [he] at hb
  change 18446744073709551615 < 4294967296 at hb
  omega

end WNear.Proofs.ValueReturnPacked
