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

theorem erase_relax (h : NearState) (p m : Nat) : erase (relax h p m) = erase h := rfl

/-- **`get` under any gas.** From a quiet host after loading, the run ends
with a gas failure on a quiet host, or done with no values and the host,
up to gas, with `"ok"` returned. -/
theorem get_any (cfg : RuntimeConfig) (fuel : Nat) (h1 : NearState)
    (hq : QuietHost h1.gas.prepaid h1.gas.maxBurnt h1)
    (hlim : withinLimit h1.config.maxReturnLen 4 = true)
    (hfuel : (runInitialized cfg.wasm fuel (.next (startSkel cfg.fees.numExtraBytesRecord h1))).2 ≠
      some (.executionIssue .fuelExhausted)) :
    (GasEnd (runInitialized cfg.wasm fuel (.next (startSkel cfg.fees.numExtraBytesRecord h1))) ∧
      QuietHost h1.gas.prepaid h1.gas.maxBurnt
        (runInitialized cfg.wasm fuel (.next (startSkel cfg.fees.numExtraBytesRecord h1))).1.host) ∨
    ∃ s, runInitialized cfg.wasm fuel (.next (startSkel cfg.fees.numExtraBytesRecord h1)) = (.done [] s, none) ∧
      erase s.host = erase (h1.selectReturnValue okBytes) := by
  set extra := cfg.fees.numExtraBytesRecord
  set c := startSkel extra h1 with hc
  set p0 := h1.gas.prepaid
  set m0 := h1.gas.maxBurnt
  have hgl : Exec.ConfigHostInvariant (GasLimits p0 m0) c := startSkel_gasLimits cfg h1
  have hqc : Exec.ConfigHostInvariant (QuietHost p0 m0) c := startSkel_quiet extra h1 hq
  -- The run with the limits raised to `Cg`, which `get_run` describes.
  set Cg := h1.gas.used + getCost cfg.wasm h1 + p0 + m0
  have hrc : (StepResult.next c).relax Cg Cg = .next (startSkel extra (relax h1 Cg Cg)) := rfl
  unfold runInitialized at hfuel ⊢
  cases hent : (chargeWasm (.next c) (entryCost cfg.wasm (.next c))).2 with
  | some e =>
    left
    simp only [hent]
    refine ⟨Or.inl ⟨e, rfl, chargeWasm_error _ _ hent⟩, ?_⟩
    exact (chargeWasm_hostInvariant quiet_chargeHost (.next c) _ hqc).host
  | none =>
    simp only [hent] at hfuel ⊢
    set r := (chargeWasm (.next c) (entryCost cfg.wasm (.next c))).1 with hr
    have hglr : MachineHostInvariant (GasLimits p0 m0) r :=
      chargeWasm_hostInvariant (fun ns cost h => by
        have hl := chargeHost_gas_limits ns cost; exact ⟨hl.1.trans h.1, hl.2.trans h.2⟩) _ _ hgl
    have hqr : MachineHostInvariant (QuietHost p0 m0) r := chargeWasm_hostInvariant quiet_chargeHost _ _ hqc
    have hfr : StoreRelaxFns r.store := by
      intro a fn h
      apply storeSkel_relaxFns extra h1 a fn
      simpa [hr, chargeWasm, chargeConfig, StepResult.store, c, startSkel] using h
    have hqA := (runMetered_hostInvariant (QuietHost p0 m0) quiet_chargeHost cfg.wasm fuel r hqr).host
    rcases runMetered_relax cfg.wasm p0 m0 Cg Cg (by omega) (by omega) fuel r hglr hfr with hge | hrel
    · exact Or.inl ⟨hge, hqA⟩
    · right
      set hB := relax h1 Cg Cg
      -- The raised run starts as `startSkel extra hB` and pays the same entry.
      have hentB : chargeWasm (.next (startSkel extra hB)) (entryCost cfg.wasm (.next (startSkel extra hB))) =
          (r.relax Cg Cg, none) := by
        rw [← hrc]
        exact chargeWasm_relax (.next c) _ Cg Cg (by show p0 ≤ Cg; omega) (by show m0 ≤ Cg; omega) hent
      have hB_run : runInitialized cfg.wasm fuel (.next (startSkel extra hB)) = runMetered cfg.wasm fuel (r.relax Cg Cg) := by
        unfold runInitialized; rw [hentB]
      have hfuelB : (runInitialized cfg.wasm fuel (.next (startSkel extra hB))).2 ≠ some (.executionIssue .fuelExhausted) := by
        rw [hB_run, hrel]; exact hfuel
      have hends := get_run cfg.wasm fuel extra hB Cg hlim
        (by
          have hv : valueReturnUse hB 4 = valueReturnUse h1 4 := valueReturnUse_erase (erase_relax h1 Cg Cg) 4
          show h1.gas.used + (8 * cfg.wasm.regularOpCost + (3 * cfg.wasm.regularOpCost + valueReturnUse hB 4)) ≤ Cg
          have hg : getCost cfg.wasm h1 =
              8 * cfg.wasm.regularOpCost + (3 * cfg.wasm.regularOpCost + valueReturnUse h1 4) := rfl
          rw [hv]; simp only [Cg, hg]; omega)
        (show Cg ≤ Cg from Nat.le_refl _) (show Cg ≤ Cg from Nat.le_refl _)
      obtain ⟨e, σ, hrcB⟩ := runInitialized_finished _ _ _ hfuelB
      rw [hrcB] at hends
      obtain ⟨rfl, hhost, -⟩ := hends
      have hdone := done_of_values (runInitialized_err _ _ _) hfuelB hrcB
      rw [hB_run, hrel] at hdone
      simp only [Prod.mk.injEq] at hdone
      obtain ⟨h1', h2'⟩ := hdone
      generalize hA : runMetered cfg.wasm fuel r = A at h1' h2' ⊢
      obtain ⟨m, err⟩ := A
      simp only at h1' h2'
      subst h2'
      cases m with
      | next c' => simp [StepResult.relax] at h1'
      | trap reason s => simp [StepResult.relax] at h1'
      | done vs s =>
        simp only [StepResult.relax, StepResult.done.injEq] at h1'
        obtain ⟨rfl, hs⟩ := h1'
        refine ⟨s, rfl, ?_⟩
        have : erase s.host = erase σ.store.host := by rw [← hs]; rfl
        rw [this, hhost, erase_selectReturnValue, erase_selectReturnValue, erase_charged, erase_relax]

end NearLogic.Skeleton
