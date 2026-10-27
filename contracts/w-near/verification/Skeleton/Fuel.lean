import Skeleton.Module

/-! The default VM fuel is sufficient for the straight-line walking body,
including its administrative return, independently of the supplied gas. -/
namespace WNear.Skeleton
open Wasm Wasm.Near

/-- The structural measure includes fifteen instructions and the empty suffix. -/
theorem moduleBody_eq : moduleBody module = 16 := by decide

/-- Even the smallest factor of the actual default fuel covers the body's
sixteen steps. No separate fuel hypothesis is required at the boundary. -/
theorem fuelFor_save (cfg : RuntimeConfig) (ctx : VMContext) :
    16 ≤ fuelFor cfg module ctx := by
  have hfactor : max 1 execLimits.maxCallDepth * (moduleBody module + 1) + 1 = 170001 := by
    rw [moduleBody_eq]
    decide
  unfold fuelFor
  rw [hfactor]
  exact Nat.le_trans (by decide : 16 ≤ 170001)
    (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

end WNear.Skeleton
