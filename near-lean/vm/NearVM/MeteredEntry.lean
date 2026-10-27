import NearVM.MeteredRules

/-! Root activation is a single real charge before the metered body. -/
namespace Wasm.Near.MeteredLogic

/-- Sufficient activation credits expose the exact initialized runner without
assuming anything about the subsequent execution. -/
theorem runInitialized_entry (cfg : WasmConfig) (fuel rest : Nat)
    (c : Config NearState)
    (hcredits : c.store.host.gas.Credits
      (activationGas cfg.regularOpCost c.locals + rest)) :
    runInitialized cfg fuel (.next c) =
      runMetered cfg fuel (.next
        {c with store := chargedStore c.store (activationGas cfg.regularOpCost c.locals)}) := by
  have hb := GasCounter.burn_credits c.store.host.gas
    (activationGas cfg.regularOpCost c.locals) rest hcredits
  simp [runInitialized, entryCost, chargeWasm, chargeConfig, chargeHost, hb.1,
    chargedStore]

end Wasm.Near.MeteredLogic
