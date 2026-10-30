import Bridge.Hosts
import NearVM.ExecutionGas

/-!
# Any method of `contract.wasm` below its gas bound

`method_below`: for any exported function `i` and any host after loading,
the run with the host's gas limits raised to `C` ends as the actual run,
up to the limits; or the actual run fails for gas, with logs that are a
prefix of the raised run's and, when the raised run ends normally, no
execution issue (given none at the start). The enough-gas proof of a
method then gives its out-of-gas case.
-/

namespace WNear.Binary

open Wasm Wasm.Near NearLogic

theorem startW_gasLimits (cfg : RuntimeConfig) (h : NearState) {i : Nat} (h1 : 48 ≤ i) (h2 : i < 955) :
    Exec.ConfigHostInvariant (GasLimits h.gas.prepaid h.gas.maxBurnt) (startW cfg h i) := by
  obtain ⟨vm, -, hvm⟩ := validate_wPrepared
  exact resolvedStart_gasLimits (resolve_wPrepared cfg) (allocate_wHosts cfg h)
    (instantiate_wPrepared cfg h vm hvm) (startWasm_wStore cfg h h1 h2)

theorem startW_relax (cfg : RuntimeConfig) (h : NearState) (i p m : Nat) :
    startW cfg (relax h p m) i = { startW cfg h i with store := relaxStore (startW cfg h i).store p m } := rfl

/-- **Any method below its gas bound.** -/
theorem method_below (cfg : RuntimeConfig) (fuel : Nat) (h : NearState) {i : Nat} (h1 : 48 ≤ i) (h2 : i < 955)
    (C : Nat) (hp : h.gas.prepaid ≤ C) (hm : h.gas.maxBurnt ≤ C) :
    let lo := runInitialized cfg.wasm fuel (.next (startW cfg h i))
    let hi := runInitialized cfg.wasm fuel (.next (startW cfg (relax h C C) i))
    (GasEnd lo ∧ lo.1.host.logs <+: hi.1.host.logs ∧
        ((∃ vs s, hi.1 = .done vs s) → lo.1.host.lastExecutionIssue = h.lastExecutionIssue) ∧
        (∀ rs ss, hi.1 = .trap rs ss → ss.host.lastExecutionIssue = h.lastExecutionIssue →
          lo.1.host.lastExecutionIssue = h.lastExecutionIssue)) ∨
      hi = (lo.1.relax C C, lo.2) := by
  intro lo hi
  rw [show hi = runInitialized cfg.wasm fuel
    (.next { startW cfg h i with store := relaxStore (startW cfg h i).store C C }) from by rw [← startW_relax]]
  exact runInitialized_relaxL cfg.wasm h.gas.prepaid h.gas.maxBurnt C C hp hm h.lastExecutionIssue fuel
    (startW cfg h i) (startW_gasLimits cfg h h1 h2) (storeRelaxFnsL_wStore cfg h) (storeLogsMono_wStore cfg h)
    ⟨storeLive_wStore cfg h _, rfl⟩

end WNear.Binary
