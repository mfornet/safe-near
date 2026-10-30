import Bridge.Methods.Panics
import Spec.Contract

/-!
# `ft_total_supply` (296) on an uninitialized contract

With no `STATE`, `state_read` returns `None` and `unwrap_or_default` calls `Contract::default`,
which `PanicOnDefault` makes panic with "The contract is not initialized". The model's step is
that panic (`step_none`, `agreesPanic_none`).
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near NearLogic NearInterface WNear.Binary

/-- The panic message of `PanicOnDefault`. -/
def notInitMsg : String := "The contract is not initialized"

theorem step_none (cfg : WNear.Config) (ctx : Context) :
    (WNear.wnear cfg).step ctx none .ftTotalSupply =
      .error { failure := .panic .notInitialized, logs := [] } := by
  rfl

/-- The model's step on no state agrees with the panic, from a host with no logs. -/
theorem agreesPanic_none (cfg : WNear.Config) (ctx : Context) (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) notInitMsg e ((WNear.wnear cfg).step ctx none .ftTotalSupply) :=
  ⟨_, step_none cfg ctx, rfl, hl.symm⟩

end WNear.Binary.FtTotalSupplyMethod
