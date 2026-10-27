import NearLogic.Examples.SkeletonModule

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

end NearLogic.Skeleton
