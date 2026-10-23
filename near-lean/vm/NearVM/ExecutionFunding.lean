import NearVM.DepositRegistry
import NearVM.MeteredLiveInvariant

namespace Wasm.Near

/-- Financial value, with explicit subsidy creation on the opposite side. -/
def Funding (funds subsidy : Nat) (ns : NearState) : Prop :=
  ns.liquidFunds + subsidy = funds + ns.subsidizedAmount

theorem HostPreservesFunding.live {fn : NearHostFn NearState}
    (hfund : HostPreservesFunding fn) (funds subsidy : Nat) :
    NearHostFn.PreservesLive (Funding funds subsidy) fn := by
  intro st args hwf
  have hf := hfund st args
  cases hr : fn.invoke st args <;> rw [hr] at hf <;>
    dsimp only [HostResult.LiveSatisfies, HostResultFunded] at hf ⊢
  · unfold Funding at hwf ⊢
    omega

theorem chargeHost_funding (ns : NearState) (cost : Nat)
    {funds subsidy : Nat} (h : Funding funds subsidy ns) :
    Funding funds subsidy (chargeHost ns cost).1 := h

/-- Concrete host resolution discharges all host funding premises. -/
theorem resolvedStart_funding {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState}
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c) :
    ConfigLiveInvariant (Funding host.liquidFunds host.subsidizedAmount) c :=
  resolvedStart_liveInvariant
    (fun fn hm => HostPreservesFunding.live (resolveMetered_funding cfg code env hresolve fn hm) _ _)
    halloc hinst hstart rfl

theorem runInitialized_liveFunding (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    {funds subsidy : Nat} (h : MachineLiveInvariant (Funding funds subsidy) m) :
    MachineLiveInvariant (Funding funds subsidy) (runInitialized cfg fuel m).1 := by
  unfold runInitialized
  dsimp only
  have hp := chargeWasm_liveInvariant (P := Funding funds subsidy)
    (fun current n h => chargeHost_funding current n h) m (entryCost cfg m) h
  split
  · exact hp
  · exact runMetered_liveInvariant _ (fun current n h => chargeHost_funding current n h) cfg fuel _ hp

/-- Successful resolved execution conserves liquid funds plus raw promise backing. -/
theorem runResolved_funding {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal}
    {vm : ValidModule} {inst : ModuleInst} {addr : Nat} {c : Config NearState} (fuel : Nat)
    (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' execLimits addr [] = some c)
    {values : List Value} {final : Store NearState}
    (hdone : (runMetered cfg.wasm fuel (.next c)).1 = .done values final) :
    Funding host.liquidFunds host.subsidizedAmount final.host := by
  have h := runMetered_liveInvariant (Funding host.liquidFunds host.subsidizedAmount)
    (fun current cost hp => chargeHost_funding current cost hp) cfg.wasm fuel (.next c)
    (resolvedStart_funding hresolve halloc hinst hstart)
  rw [hdone] at h
  exact h.2

end Wasm.Near
