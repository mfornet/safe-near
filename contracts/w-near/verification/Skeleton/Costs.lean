import Skeleton.Module

/-! Symbolic costs shared by skeleton contracts and their executable checkers. -/
namespace WNear.Skeleton
open Wasm Wasm.Near

/-- An input-size failure pays loading, eight activation units, two guest
instructions and the two fixed input-host charges. This bound reads no run. -/
def inputFailureCost (cfg : RuntimeConfig) : Nat :=
  cfg.wasm.extCosts.cost "contract_loading_base" + 10 * cfg.wasm.regularOpCost +
    cfg.wasm.extCosts.cost "base" + cfg.wasm.extCosts.cost "write_register_base"

end WNear.Skeleton
