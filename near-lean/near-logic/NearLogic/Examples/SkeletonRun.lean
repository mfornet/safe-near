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

end NearLogic.Skeleton
