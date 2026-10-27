import NearLogic.Examples.SkeletonModule
import NearLogic.Outcome

/-!
# The skeleton's `get`, run

`get_run`: the method, started as `runAttempt` starts it after loading,
pays its entry activation and ends as `get_adequate` says.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near Iris.ProgramLogic

theorem entryCost_skel (cfg : WasmConfig) (extra : Nat) (h : NearState) :
    entryCost cfg (.next (startSkel extra h)) = 8 * cfg.regularOpCost := by
  simp [entryCost, activationGas, Config.locals, startSkel, entryThread]

theorem dataMem_facts : dataMem.wf = true ∧ ∀ k, k < 4 → k < dataMem.byteSize ∧ dataMem.read8 k = okBytes[k]! := by
  obtain ⟨m', hw, hwf, hsz, -, hrd⟩ := writeBytes_spec (Memory.new_wf 1024 (some 2048)) (addr := 0)
    (bytes := ⟨okBytes.toArray⟩) (by simp [Memory.new_byteSize, okBytes, pageSize, ByteArray.size])
  have hd : dataMem = m' := by unfold dataMem; rw [hw]; rfl
  rw [hd]
  refine ⟨hwf, fun k hk => ⟨?_, ?_⟩⟩
  · rw [hsz, Memory.new_byteSize]; simp [pageSize]; omega
  · rw [hrd]
    have : (0 ≤ k ∧ k < 0 + (⟨okBytes.toArray⟩ : ByteArray).size) := ⟨Nat.zero_le _, by simp [okBytes, ByteArray.size]; omega⟩
    rw [if_pos this]
    obtain _ | _ | _ | _ | k := k <;> first | rfl | omega

/-- `get`, from the host `h1` after loading, with room for its gas within
`Cg`: it ends with no values, the host with `"ok"` returned (gas aside) and
at most `Cg` gas used. -/
theorem get_run (cfg : WasmConfig) (fuel extra : Nat) (h1 : NearState) (Cg : Nat)
    (hlim : withinLimit h1.config.maxReturnLen 4 = true)
    (hgas : h1.gas.used + (8 * cfg.regularOpCost + (3 * cfg.regularOpCost + valueReturnUse h1 4)) ≤ Cg)
    (hC1 : Cg ≤ h1.gas.maxBurnt) (hC2 : Cg ≤ h1.gas.prepaid) :
    match resultCode cfg (runInitialized cfg fuel (.next (startSkel extra h1))) with
    | (.finished e, σ) => GetEnds Cg (charged h1 (8 * cfg.regularOpCost)) e σ
    | (.running .., _) => True := by
  have hentry : chargeWasm (.next (startSkel extra h1)) (entryCost cfg (.next (startSkel extra h1))) =
      (.next { startSkel extra h1 with store := { storeSkel extra h1 with
        host := charged h1 (8 * cfg.regularOpCost) } }, none) := by
    rw [entryCost_skel, chargeWasm_ok (C := Cg) (by simp [startSkel, storeSkel, StepResult.store]; omega)
      (by simpa [startSkel, storeSkel, StepResult.store] using hC1)
      (by simpa [startSkel, storeSkel, StepResult.store] using hC2)]
    rfl
  obtain ⟨hwf, hbytes⟩ := dataMem_facts
  have hu : (charged h1 (8 * cfg.regularOpCost)).gas.used = h1.gas.used + 8 * cfg.regularOpCost :=
    charged_gas_used _ _
  have hvr : valueReturnUse (charged h1 (8 * cfg.regularOpCost)) 4 = valueReturnUse h1 4 :=
    valueReturnUse_erase (erase_charged _ _) 4
  exact runInitialized_ending_state cfg fuel _ _ _ hentry
    (get_adequate cfg execLimits extra { storeSkel extra h1 with host := charged h1 (8 * cfg.regularOpCost) }
      #[] 0 0 0 instSkel dataMem Cg rfl rfl rfl rfl rfl hwf hbytes (by simpa [charged] using hlim)
      (by simp only [hu, hvr]; omega) (by simpa [charged] using hC1) (by simpa [charged] using hC2))

/-- A run that did not exhaust its fuel did not stop at a running thread:
`runMetered` stops running only for want of fuel or at a failed charge. -/
theorem runMetered_finished (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : (runMetered cfg fuel m).2 ≠ some (.executionIssue .fuelExhausted)) :
    ∃ e σ, resultCode cfg (runMetered cfg fuel m) = (.finished e, σ) := by
  induction fuel generalizing m with
  | zero =>
    cases m with
    | next c => exact absurd rfl h
    | done vs s => exact ⟨_, _, by rw [runMetered_done]; rfl⟩
    | trap r s => exact ⟨_, _, by rw [runMetered_trapped]; rfl⟩
  | succ fuel ih =>
    cases m with
    | done vs s => exact ⟨_, _, by rw [runMetered_done]; rfl⟩
    | trap r s => exact ⟨_, _, by rw [runMetered_trapped]; rfl⟩
    | next c =>
      unfold runMetered at h ⊢
      cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
      | some e => simp only [h1]; exact ⟨_, _, rfl⟩
      | none =>
        simp only [h1] at h ⊢
        cases h2 : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
            (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
              (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 with
        | some e => simp only [h2]; exact ⟨_, _, rfl⟩
        | none =>
          simp only [h2] at h ⊢
          exact ih _ h

theorem runInitialized_finished (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : (runInitialized cfg fuel m).2 ≠ some (.executionIssue .fuelExhausted)) :
    ∃ e σ, resultCode cfg (runInitialized cfg fuel m) = (.finished e, σ) := by
  unfold runInitialized at h ⊢
  simp only at h ⊢
  split
  · exact ⟨_, _, rfl⟩
  · rename_i h2
    rw [h2] at h
    exact runMetered_finished cfg fuel _ h

/-- With at least `fuelFor`, `get` never stops for want of fuel. -/
theorem get_fuel (cfg : RuntimeConfig) (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (size : Nat) (hpos : 0 < minOpCost cfg.wasm) {fuel : Nat} (hfuel : fuelFor cfg skelModule ctx ≤ fuel) :
    (runInitialized cfg.wasm fuel (.next (startSkel cfg.fees.numExtraBytesRecord
      (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1))).2 ≠
      some (.executionIssue .fuelExhausted) := by
  obtain ⟨vm, -, hvm⟩ := validate_skel
  set host1 := (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1
  have halloc : (HostEnv.allocate (Store.empty host1)
      { funcs := [metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn] }) =
      ({ funcs := #[.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn],
         host := host1 }, [.func 0]) := rfl
  have hinst := instantiate_skel cfg.fees.numExtraBytesRecord host1 vm hvm
  have hres : resolveMetered cfg skelPrepared =
      .ok { funcs := [metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn] } := rfl
  have hstart : Exec.startWasm (storeSkel cfg.fees.numExtraBytesRecord host1) execLimits
      instSkel.funcAddrs[1]! [] = some (startSkel cfg.fees.numExtraBytesRecord host1) := rfl
  have hfloor0 : GasFloor 0 ctx.prepaidGas (ctx.maxBurnt cfg) (VMContext.toNearState cfg ctx storage) := by
    refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl, ?_⟩
    unfold VMContext.toNearState VMContext.maxBurnt
    cases ctx.viewConfig <;> rfl
  have hinv : FuelInv ctx.prepaidGas (ctx.maxBurnt cfg) (startSkel cfg.fees.numExtraBytesRecord host1) :=
    ⟨startWasm_bounded hstart, resolved_floorHosts hres halloc hinst, applyCharges_floor _ _ hfloor0⟩
  have hspan : span (startSkel cfg.fees.numExtraBytesRecord host1) ≤
      max 1 execLimits.maxCallDepth * (moduleBody skelModule + 1) := by
    unfold span
    have hb := resolved_maxBody halloc hinst
    rw [hvm] at hb
    have : moduleBody skelPrepared = moduleBody skelModule := rfl
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (this ▸ hb) 1)
  apply runInitialized_enough_fuel hpos hinv
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hspan 1)) hfuel

/-- `runMetered` reports nothing, a failed charge, or fuel exhaustion. -/
theorem runMetered_err (cfg : WasmConfig) (fuel : Nat) (m : Machine) :
    (runMetered cfg fuel m).2 = none ∨ (∃ e, (runMetered cfg fuel m).2 = some (.hostError e)) ∨
      (runMetered cfg fuel m).2 = some (.executionIssue .fuelExhausted) := by
  induction fuel generalizing m with
  | zero => cases m <;> simp [runMetered]
  | succ fuel ih =>
    cases m with
    | done vs s => rw [runMetered_done]; simp
    | trap r s => rw [runMetered_trapped]; simp
    | next c =>
      unfold runMetered
      cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
      | some e => simp [h1]
      | none =>
        simp only [h1]
        cases h2 : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
            (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
              (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 with
        | some e => simp [h2]
        | none => simp only [h2]; exact ih _

theorem runInitialized_err (cfg : WasmConfig) (fuel : Nat) (m : Machine) :
    (runInitialized cfg fuel m).2 = none ∨ (∃ e, (runInitialized cfg fuel m).2 = some (.hostError e)) ∨
      (runInitialized cfg fuel m).2 = some (.executionIssue .fuelExhausted) := by
  unfold runInitialized
  cases h : (chargeWasm m (entryCost cfg m)).2 with
  | some e => simp [h]
  | none => simp only [h]; exact runMetered_err cfg fuel _

/-- A run that ended with values, and did not exhaust its fuel, is done. -/
theorem done_of_values {cfg : WasmConfig} {r : Machine × Option FunctionCallError} {vs : List Value} {σ : MStore}
    (herr : r.2 = none ∨ (∃ e, r.2 = some (.hostError e)) ∨ r.2 = some (.executionIssue .fuelExhausted))
    (hfuel : r.2 ≠ some (.executionIssue .fuelExhausted))
    (h : resultCode cfg r = (.finished (.values vs), σ)) : r = (.done vs σ.store, none) := by
  obtain ⟨m, err⟩ := r
  simp only at herr hfuel
  rcases herr with rfl | ⟨e, rfl⟩ | rfl
  · cases m with
    | next c => simp [resultCode] at h
    | done vs' s => simp only [resultCode, Prod.mk.injEq, MCode.finished.injEq, Ending.values.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h; rfl
    | trap r s => simp [resultCode] at h
  · simp [resultCode] at h
  · exact absurd rfl hfuel

/-- The gas `get` uses after loading: its entry activation, three
instructions and `value_return`. -/
def getCost (cfg : WasmConfig) (h : NearState) : Nat :=
  8 * cfg.regularOpCost + (3 * cfg.regularOpCost + valueReturnUse h 4)

/-- `run` on `get`, with room for loading and `get` within `Cg`: no abort,
`"ok"` returned, no receipts, at most `Cg` used, and the account's balance,
usage, logs and storage as the context has them. -/
theorem get_vmOutcome (cfg : RuntimeConfig) (size : Nat) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) (Cg : Nat)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits skelModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hret : withinLimit (ctx.toNearState cfg storage).config.maxReturnLen 4 = true)
    (hgas : (ctx.toNearState cfg storage).gas.used +
      chargesUse (ctx.toNearState cfg storage) (loadingCharges size) +
        getCost cfg.wasm (ctx.toNearState cfg storage) ≤ Cg)
    (hC1 : Cg ≤ (ctx.toNearState cfg storage).gas.maxBurnt)
    (hC2 : Cg ≤ (ctx.toNearState cfg storage).gas.prepaid) :
    let o := run cfg skelModule size "get" ctx storage
    o.aborted = none ∧ o.returnData = .value okBytes ∧ o.receipts = [] ∧ o.usedGas ≤ Cg ∧
      o.logs = [] ∧ o.balance = ctx.accountBalance + ctx.attachedDeposit ∧
      o.storageUsage = ctx.storageUsage % 2 ^ 64 ∧
      o.storage = finalStorage (ctx.toNearState cfg storage) := by
  set h0 := ctx.toNearState cfg storage
  obtain ⟨hok, hch⟩ := applyCharges_ok h0 (loadingCharges size) (C := Cg) (by omega) hC1 hC2
  set h1 := (applyCharges h0 (loadingCharges size)).1
  have hfuel := get_fuel cfg ctx storage size hpos (Nat.le_refl (fuelFor cfg skelModule ctx))
  have hrun : runAttempt cfg skelModule size "get" ctx storage =
      outcomeOfExecution ctx storage
        (runInitialized cfg.wasm (fuelFor cfg skelModule ctx) (.next (startSkel cfg.fees.numExtraBytesRecord h1))).1
        (runInitialized cfg.wasm (fuelFor cfg skelModule ctx) (.next (startSkel cfg.fees.numExtraBytesRecord h1))).2 := by
    rcases runAttempt_skel cfg size ctx storage (fuelFor cfg skelModule ctx) hlimit hmin hmax with
      ⟨e, he, -⟩ | ⟨-, h⟩
    · rw [hok] at he; cases he
    · exact h
  have hends := get_run cfg.wasm (fuelFor cfg skelModule ctx) cfg.fees.numExtraBytesRecord h1 Cg
    (by rw [show h1.config = h0.config from hch.config]; exact hret)
    (by unfold getCost at hgas
        have : valueReturnUse h1 4 = valueReturnUse h0 4 := valueReturnUse_erase hch.erase 4
        rw [hch.used, this]; omega)
    (by rw [hch.maxBurnt]; exact hC1) (by rw [hch.prepaid]; exact hC2)
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished _ _ _ hfuel
  rw [hrc] at hends
  obtain ⟨rfl, hhost, hused⟩ := hends
  have hdone := done_of_values (runInitialized_err _ _ _) hfuel hrc
  -- The final host is the initial one, with "ok" returned, up to gas.
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (erase x) = f x) →
      f σ.store.host = f (h0.selectReturnValue okBytes) := by
    intro α f hfe
    rw [erase_field hhost f hfe]
    have h1e : erase ((charged h1 (8 * cfg.wasm.regularOpCost)).selectReturnValue okBytes) =
        erase (h0.selectReturnValue okBytes) := by
      rw [erase_selectReturnValue, erase_selectReturnValue, erase_charged, hch.erase]
    exact erase_field h1e f hfe
  have hp : σ.store.host.promises = [] := hf NearState.promises fun _ => rfl
  have hr : σ.store.host.returnedPromise = none := hf NearState.returnedPromise fun _ => rfl
  have hw : σ.store.host.gasWeights = [] := hf NearState.gasWeights fun _ => rfl
  have hrd : σ.store.host.returnData = some okBytes := hf NearState.returnData fun _ => rfl
  have hlogs : σ.store.host.logs = [] := hf NearState.logs fun _ => rfl
  have hbal : σ.store.host.context.accountBalance = ctx.accountBalance + ctx.attachedDeposit :=
    hf (fun x => x.context.accountBalance) fun _ => rfl
  have husage : σ.store.host.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
    hf (fun x => x.context.storageUsage) fun _ => rfl
  have hstore : finalStorage σ.store.host = finalStorage h0 := hf finalStorage fun _ => rfl
  obtain ⟨ha, hrec, hret', husd, -, -, hb, hu, hl, hs⟩ :=
    outcomeOfExecution_noPromises ctx storage [] σ.store hp hr hw
  simp only [run]
  rw [hrun, hdone]
  rw [checkReceipts_noReceipts _ _ _ _ hrec (by rw [hret']; intro i; simp [hrd])]
  refine ⟨ha, by rw [hret']; simp [hrd], hrec, by rw [husd]; exact hused, by rw [hl, logsOf, hlogs]; rfl,
    by rw [hb, hbal], by rw [hu, husage]; simp, by rw [hs, hstore]⟩

end NearLogic.Skeleton
