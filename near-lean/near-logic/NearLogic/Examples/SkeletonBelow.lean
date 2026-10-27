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

/-! ## The VM outcome -/

/-- A gas failure, as the VM reports it: aborted with a gas error, nothing
returned, no receipts and no logs. -/
def GasFailure (o : VMOutcome) : Prop :=
  ∃ e, isGasError e ∧ o.aborted = some (.hostError e) ∧ o.returnData = .none ∧ o.receipts = [] ∧ o.logs = []

theorem outcome_gasEnd (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (r : Machine × Option FunctionCallError) (hg : GasEnd r)
    (hi : r.1.host.lastExecutionIssue = none) (hl : r.1.host.logs = []) :
    GasFailure (outcomeOfExecution ctx storage r.1 r.2) := by
  obtain ⟨m, err⟩ := r
  rcases hg with ⟨e, he, hge⟩ | ⟨hn, reason, s, e, hm, hle, hge⟩
  · simp only at he hi hl
    subst he
    exact ⟨e, hge, rfl, rfl, rfl, by simp [outcomeOfExecution, logsOf, hl]⟩
  · simp only at hn hm hi hl
    subst hn hm
    have ht : trapError reason s.host = .hostError e := by
      simp only [StepResult.host] at hi
      simp [trapError, hi, hle]
    have hs : (StepResult.trap reason s).host = s.host := rfl
    rw [hs] at hl
    refine ⟨e, hge, ?_, rfl, rfl, ?_⟩
    · simp [outcomeOfExecution, hs, ht]
    · simp [outcomeOfExecution, hs, ht, logsOf, hl]

theorem gasFailure_checkReceipts {o : VMOutcome} (h : GasFailure o) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) : GasFailure (o.checkReceipts balance usage storage) := by
  obtain ⟨e, he, ha, hrd, hr, hl⟩ := h
  rw [checkReceipts_noReceipts o balance usage storage hr (by rw [hrd]; intro i; simp)]
  exact ⟨e, he, ha, hrd, hr, hl⟩

/-- **`get` under any gas, at the VM.** The call fails for gas, or it
returns `"ok"` with the effects it has with enough gas. -/
theorem get_vm_any (cfg : RuntimeConfig) (size : Nat) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8))
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits skelModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hret : withinLimit (ctx.toNearState cfg storage).config.maxReturnLen 4 = true) :
    let o := run cfg skelModule size "get" ctx storage
    GasFailure o ∨
      (o.aborted = none ∧ o.returnData = .value okBytes ∧ o.receipts = [] ∧ o.distributedGas = 0 ∧
        o.logs = [] ∧ o.balance = ctx.accountBalance + ctx.attachedDeposit ∧
        o.storageUsage = ctx.storageUsage % 2 ^ 64 ∧ o.storage = finalStorage (ctx.toNearState cfg storage)) := by
  set h0 := ctx.toNearState cfg storage
  set h1 := (applyCharges h0 (loadingCharges size)).1
  have he1 : erase h1 = erase h0 := applyCharges_erase h0 (loadingCharges size)
  simp only [run]
  rcases runAttempt_skel cfg size ctx storage (fuelFor cfg skelModule ctx) hlimit hmin hmax with
    ⟨e, he, hrun⟩ | ⟨-, hrun⟩
  · left
    rw [hrun]
    apply gasFailure_checkReceipts
    exact ⟨e, applyCharges_error h0 _ he, rfl, rfl, rfl, rfl⟩
  have hq : QuietHost h1.gas.prepaid h1.gas.maxBurnt h1 :=
    ⟨rfl, rfl, erase_field he1 NearState.lastExecutionIssue (fun _ => rfl),
      erase_field he1 NearState.logs (fun _ => rfl)⟩
  have hlim : withinLimit h1.config.maxReturnLen 4 = true := by
    rw [erase_field he1 NearState.config (fun _ => rfl)]; exact hret
  have hfuel := get_fuel cfg ctx storage size hpos (Nat.le_refl (fuelFor cfg skelModule ctx))
  rw [hrun]
  rcases get_any cfg (fuelFor cfg skelModule ctx) h1 hq hlim hfuel with ⟨hg, hqA⟩ | ⟨s, hs, hhost⟩
  · left
    apply gasFailure_checkReceipts
    exact outcome_gasEnd ctx storage _ hg hqA.2.2.1 hqA.2.2.2
  · right
    rw [hs]
    have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (erase x) = f x) →
        f s.host = f (h0.selectReturnValue okBytes) := by
      intro α f hfe
      rw [erase_field hhost f hfe]
      have h1e : erase (h1.selectReturnValue okBytes) = erase (h0.selectReturnValue okBytes) := by
        rw [erase_selectReturnValue, erase_selectReturnValue, he1]
      exact erase_field h1e f hfe
    have hp : s.host.promises = [] := hf NearState.promises fun _ => rfl
    have hr : s.host.returnedPromise = none := hf NearState.returnedPromise fun _ => rfl
    have hw : s.host.gasWeights = [] := hf NearState.gasWeights fun _ => rfl
    have hrd : s.host.returnData = some okBytes := hf NearState.returnData fun _ => rfl
    have hlogs : s.host.logs = [] := hf NearState.logs fun _ => rfl
    have hbal : s.host.context.accountBalance = ctx.accountBalance + ctx.attachedDeposit :=
      hf (fun x => x.context.accountBalance) fun _ => rfl
    have husage : s.host.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
      hf (fun x => x.context.storageUsage) fun _ => rfl
    have hstore : finalStorage s.host = finalStorage h0 := hf finalStorage fun _ => rfl
    obtain ⟨ha, hrec, hret', -, -, hdist, hb, hu, hl, hst⟩ :=
      outcomeOfExecution_noPromises ctx storage [] s hp hr hw
    rw [checkReceipts_noReceipts _ _ _ _ hrec (by rw [hret']; intro i; simp [hrd])]
    exact ⟨ha, by rw [hret']; simp [hrd], hrec, hdist, by rw [hl, logsOf, hlogs]; rfl,
      by rw [hb, hbal], by rw [hu, husage]; simp, by rw [hst, hstore]⟩

end NearLogic.Skeleton
