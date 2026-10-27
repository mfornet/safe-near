import NearLogic.Examples.SkeletonRun
import NearLogic.RelaxRun
import NearVM.ExecutionGas

/-!
# The walking skeleton below its gas bound

Whatever gas is attached, `get` either fails for gas, with no logs and no
execution issue, or ends as it does with enough gas. The run is related to
the same run with its gas limits raised to the bound (`runMetered_relax`),
which `get_run` describes.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near

/-- The linked `value_return` keeps the host quiet. -/
theorem valueReturn_preservesQuiet (extra p0 m0 : Nat) :
    Exec.HostFn.Preserves (QuietHost p0 m0) (metered extra "value_return" valueReturnFn).toHostFn := by
  intro h mem args hq
  have := valueReturn_quiet extra { mem := mem.getD (Memory.new 0 none), host := h } args hq
  simp only [NearHostFn.toHostFn]
  cases hr : (metered extra "value_return" valueReturnFn).invoke { mem := mem.getD (Memory.new 0 none), host := h } args <;>
    rw [hr] at this <;> exact this

/-- The only host function of the instantiated store is `value_return`. -/
theorem storeSkel_host {extra : Nat} {h : NearState} {fn : HostFn NearState}
    (hm : FuncInst.host fn ∈ (storeSkel extra h).funcs) :
    fn = (metered extra "value_return" valueReturnFn).toHostFn := by
  simp only [storeSkel, Array.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h1 | h1
  · cases h1; rfl
  · cases h1

theorem storeSkel_relaxFns (extra : Nat) (h : NearState) : StoreRelaxFns (storeSkel extra h) := by
  intro a fn hfn
  rw [storeSkel_host (Array.mem_of_getElem? hfn)]
  exact valueReturn_relaxFn extra

/-- The start configuration keeps the gas limits it starts with. -/
theorem startSkel_gasLimits (cfg : RuntimeConfig) (h : NearState) :
    Exec.ConfigHostInvariant (GasLimits h.gas.prepaid h.gas.maxBurnt) (startSkel cfg.fees.numExtraBytesRecord h) := by
  obtain ⟨vm, -, hvm⟩ := validate_skel
  have halloc : (HostEnv.allocate (Store.empty h)
      { funcs := [metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn] }) =
      ({ funcs := #[.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn],
         host := h }, [.func 0]) := rfl
  have hres : resolveMetered cfg skelPrepared =
      .ok { funcs := [metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn] } := rfl
  have hstart : Exec.startWasm (storeSkel cfg.fees.numExtraBytesRecord h) execLimits
      instSkel.funcAddrs[1]! [] = some (startSkel cfg.fees.numExtraBytesRecord h) := rfl
  exact resolvedStart_gasLimits hres halloc (instantiate_skel _ h vm hvm) hstart

/-- The start configuration keeps the host quiet. -/
theorem startSkel_quiet (extra : Nat) (h : NearState) (hq : QuietHost h.gas.prepaid h.gas.maxBurnt h) :
    Exec.ConfigHostInvariant (QuietHost h.gas.prepaid h.gas.maxBurnt) (startSkel extra h) :=
  ⟨fun fn hm => by rw [storeSkel_host hm]; exact valueReturn_preservesQuiet extra _ _, hq⟩

theorem quiet_chargeHost {p0 m0 : Nat} (ns : NearState) (cost : Nat) (hq : QuietHost p0 m0 ns) :
    QuietHost p0 m0 (chargeHost ns cost).1 := by
  have hl := chargeHost_gas_limits ns cost
  exact ⟨hl.1.trans hq.1, hl.2.trans hq.2.1, hq.2.2.1, hq.2.2.2⟩

end NearLogic.Skeleton
