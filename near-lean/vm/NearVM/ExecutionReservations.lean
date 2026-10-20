import NearVM.PromiseGas
import NearVM.SuccessInvariant

namespace Wasm.Near

/-- Host charging must use the same fee table and protocol flag as the
receipt valuation. The concrete registry must preserve this entire invariant. -/
def ReservationInvariant (fees : ActionFees) (ethEnabled : Bool) (ns : NearState) : Prop :=
  ns.fees = fees ∧ ns.config.ethImplicitAccounts = ethEnabled ∧ GasBacked fees ethEnabled ns

/-- Successful instruction/frame charging cannot discard reserved promise gas. -/
theorem chargeWasm_success_gasBacked (fees : ActionFees) (ethEnabled : Bool)
    (config : SmallStep.Config NearState) (cost : Nat)
    (hsuccess : (chargeWasm config cost).2 = none) (h : GasBacked fees ethEnabled config.store.wasm.host) :
    GasBacked fees ethEnabled (chargeWasm config cost).1.store.wasm.host := by
  have hg := GasCounter.deduct_success config.store.wasm.host.gas cost cost (Nat.le_refl _) hsuccess
  have hp : (chargeWasm config cost).1.store.wasm.host.gas.promises = config.store.wasm.host.gas.promises := by
    simpa only [chargeWasm, GasCounter.burn, Nat.sub_self, Nat.add_zero] using hg.2.1
  unfold GasBacked at h ⊢
  rw [hp]
  exact h

theorem chargeWasm_success_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (config : SmallStep.Config NearState) (cost : Nat)
    (hsuccess : (chargeWasm config cost).2 = none)
    (h : ReservationInvariant fees ethEnabled config.store.wasm.host) :
    ReservationInvariant fees ethEnabled (chargeWasm config cost).1.store.wasm.host :=
  ⟨h.1, h.2.1, chargeWasm_success_gasBacked fees ethEnabled config cost hsuccess h.2.2⟩

/-- This compositional theorem requires the live host invariant explicitly.
The concrete registry proof must supply it; successful gas charging is derived
from the executable run, rather than required on failed/saturated states. -/
theorem runInitialized_success_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (h : ConfigLiveInvariant (ReservationInvariant fees ethEnabled) config)
    (hsuccess : (runInitialized cfg fuel config).2 = none) :
    (runInitialized cfg fuel config).1.LiveHost (ReservationInvariant fees ethEnabled) := by
  exact (runInitialized_success_liveInvariant _ (chargeWasm_success_reservationInvariant fees ethEnabled)
    cfg fuel config h hsuccess).2

/-- Actual metered execution and outcome conversion compose without assuming a
financial equation at the outcome. The remaining premise is host preservation
of fee/config identity and raw promise gas backing. -/
theorem runInitialized_outcome_gas_backing (fees : ActionFees) (ethEnabled : Bool)
    (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (ctx : VMContext) (storage : List (Bytes × Bytes))
    (h : ConfigLiveInvariant (ReservationInvariant fees ethEnabled) config)
    (hsuccess : (outcomeOfExecution ctx storage (runInitialized cfg fuel config).1
      (runInitialized cfg fuel config).2).aborted = none) :
    let outcome := outcomeOfExecution ctx storage (runInitialized cfg fuel config).1 (runInitialized cfg fuel config).2
    outcome.usedGas = outcome.burntGas + receiptsGas fees ethEnabled outcome.receipts := by
  have herr := outcomeOfExecution_success_error_none ctx storage _ _ hsuccess
  have hl := runInitialized_success_reservationInvariant fees ethEnabled cfg fuel config h herr
  have hf := outcomeOfExecution_success_live ctx storage _ _ hsuccess hl
  exact outcomeOfExecution_success_gas_backing fees ethEnabled ctx storage _ _ hsuccess hf.2.2

end Wasm.Near
