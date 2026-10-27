import NearRuntime.Boundary
import NearVM.GasCredits

/-! Initial machine credits are precisely the receipt's two gas limits. -/
namespace Near.Boundary
open Wasm Wasm.Near NearInterface

/-- The runtime initializes burnt and reserved gas to zero. Reserving `cost`
therefore means it fits both prepaid gas and the protocol burn cap. -/
theorem initial_credits_iff (ctx : Context) (storage : List (Bytes × Bytes)) (cost : Nat) :
    ((toVMContext ctx).toNearState ctx.protocol storage).gas.Credits cost ↔
      cost ≤ ctx.gasLimit := by
  simp only [GasCounter.Credits, GasCounter.used, VMContext.toNearState, toVMContext,
    Context.gasLimit, Nat.zero_add]
  omega

end Near.Boundary
