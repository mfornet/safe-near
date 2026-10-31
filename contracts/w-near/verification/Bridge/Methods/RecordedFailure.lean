import Bridge.Methods.Panics

namespace WNear.Binary.RecordedFailure
open Wasm Wasm.Near NearLogic NearInterface ContractModel WNear.Binary

/-- Named complete method-run obligation consumed by the recorded-failure receipt composition. -/
def RecordedFailureRun (cfg : RuntimeConfig) (i : Nat) (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) : Prop :=
  MethodPanicsR cfg i Pre cost Post

/-- A host with the exact recorded error and no execution issue. -/
def FailureHost (error : HostError) (e : NearState) : Prop :=
  e.lastError = some error ∧ e.lastExecutionIssue = none

/-- A VM outcome with the exact recorded host error and the host's logs. -/
def FailureOutcome (o : VMOutcome) (error : HostError) (e : NearState) : Prop :=
  o.aborted = some (.hostError error) ∧ o.returnData = .none ∧ o.receipts = [] ∧
    o.logs = logsOf e

/-- A run that trapped after a panic. -/
theorem outcome_failure (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (r : Trap)
    (s : Store NearState) {error : HostError} (hp : FailureHost error (erase s.host)) :
    let o := (outcomeOfExecution ctx storage (.trap r s) none).checkReceipts ctx.accountBalance
      ctx.storageUsage storage
    FailureOutcome o error s.host ∧ o.burntGas = s.host.gas.burnt := by
  obtain ⟨he, hi⟩ := hp
  have he' : s.host.lastError = some error := he
  have hi' : s.host.lastExecutionIssue = none := hi
  have ht : trapError r s.host = .hostError error := by simp [trapError, hi', he']
  have hs : (StepResult.trap r s).host = s.host := rfl
  rw [checkReceipts_noReceipts _ _ _ _ (by simp [outcomeOfExecution, hs, ht])
    (by simp [outcomeOfExecution, hs, ht])]
  simp [outcomeOfExecution, hs, ht, FailureOutcome]

/-- **Enough gas, at the VM**: the run records the exact host failure specified by `Post`. -/
theorem method_vmOutcomeFailure (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (error : HostError) (Cg : Nat)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : RecordedFailureRun cfg i Pre cost Post) (hpre : Pre (erase (ctx.toNearState cfg storage)))
    (hend : ∀ e, Post (erase (ctx.toNearState cfg storage)) e → FailureHost error e)
    (hgas : (ctx.toNearState cfg storage).gas.used +
      chargesUse (ctx.toNearState cfg storage) (loadingCharges size) +
        cost (erase (ctx.toNearState cfg storage)) ≤ Cg)
    (hC1 : Cg ≤ (ctx.toNearState cfg storage).gas.maxBurnt)
    (hC2 : Cg ≤ (ctx.toNearState cfg storage).gas.prepaid) :
    let o := run cfg wNearModule size method ctx storage
    ∃ e, Post (erase (ctx.toNearState cfg storage)) e ∧ FailureOutcome o error e ∧ o.burntGas ≤ Cg := by
  set h0 := ctx.toNearState cfg storage
  obtain ⟨hok, hch⟩ := applyCharges_ok h0 (loadingCharges size) (C := Cg) (by omega) hC1 hC2
  set hl := (applyCharges h0 (loadingCharges size)).1
  have he1 : erase hl = erase h0 := applyCharges_erase h0 _
  have hfuel := method_fuel cfg size ctx storage h1 h2 hpos
  have hrun : runAttempt cfg wNearModule size method ctx storage =
      outcomeOfExecution ctx storage
        (runInitialized cfg.wasm (fuelFor cfg wNearModule ctx) (.next (startW cfg hl i))).1
        (runInitialized cfg.wasm (fuelFor cfg wNearModule ctx) (.next (startW cfg hl i))).2 := by
    rcases runAttempt_wnear cfg size method ctx storage (fuelFor cfg wNearModule ctx) i hlimit hmin hmax
      hname hexp hft h1 h2 with ⟨e, he, -⟩ | ⟨-, h⟩
    · rw [hok] at he; cases he
    · exact h
  obtain ⟨r, s, hs, hpost, hused⟩ := hspec (fuelFor cfg wNearModule ctx) hl Cg (by rw [he1]; exact hpre)
    (by rw [he1, hch.used]; omega) (by rw [hch.maxBurnt]; exact hC1) (by rw [hch.prepaid]; exact hC2) hfuel
  rw [he1] at hpost
  obtain ⟨hpo, hu⟩ := outcome_failure ctx storage r s (hend _ hpost)
  refine ⟨erase s.host, hpost, ?_⟩
  simp only [run]
  rw [hrun, hs]
  refine ⟨hpo, ?_⟩
  rw [hu]
  exact Nat.le_trans (gasUsed_burnt _) hused

/-- **Any gas, at the VM**: a gas or recorded-proof failure, or the exact recorded host failure. Only the run with the
limits raised, which records no proof, needs `Pre`. -/
theorem method_vm_anyFailure (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (error : HostError)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : RecordedFailureRun cfg i Pre cost Post) (hpre : Pre (eraseP (ctx.toNearState cfg storage)))
    (hend : ∀ e, Post (eraseP (ctx.toNearState cfg storage)) e → FailureHost error e) :
    let o := run cfg wNearModule size method ctx storage
    ∃ e, Post (eraseP (ctx.toNearState cfg storage)) e ∧
      (GasFailureUpTo o (logsOf e) ∨ FailureOutcome o error e) := by
  set h0 := ctx.toNearState cfg storage
  set hl := (applyCharges h0 (loadingCharges size)).1
  have he1 : erase hl = erase h0 := applyCharges_erase h0 _
  set F0 := fuelFor cfg wNearModule ctx
  set C := hl.gas.used + cost (eraseP h0) + hl.gas.prepaid + hl.gas.maxBurnt
  have hfuel0 := method_fuel cfg size ctx storage h1 h2 hpos
  have hlo : runInitialized cfg.wasm (F0 + wFuel cfg.wasm C) (.next (startW cfg hl i)) =
      runInitialized cfg.wasm F0 (.next (startW cfg hl i)) :=
    runInitialized_extra_fuel _ _ _ hfuel0 _
  have hfl : GasFloor 0 ctx.prepaidGas (ctx.maxBurnt cfg) hl := loaded_floor cfg size ctx storage
  obtain ⟨-, hb1, -, -, hmb⟩ := hfl
  have hflr : GasFloor 0 C C (relax hl C C) := by
    refine ⟨Nat.zero_le _, ?_, ?_, rfl, rfl⟩ <;>
    · show hl.gas.burnt ≤ C
      omega
  have hfuelHi := startW_enough_fuel cfg (relax hl C C) h1 h2 hflr hpos
    (fuel := F0 + wFuel cfg.wasm C) (Nat.le_add_left _ _)
  obtain ⟨r', s', hs', hpost', -⟩ := hspec (F0 + wFuel cfg.wasm C) (relax hl C C) C
    (by show Pre (eraseP hl); rw [eraseP_of_erase he1]; exact hpre)
    (by show hl.gas.used + cost (eraseP hl) ≤ C; rw [eraseP_of_erase he1]; omega) (Nat.le_refl _) (Nat.le_refl _)
    hfuelHi
  have hpost : Post (eraseP h0) (erase s'.host) := by
    have : erase (relax hl C C) = eraseP hl := rfl
    rw [this, eraseP_of_erase he1] at hpost'
    exact hpost'
  refine ⟨erase s'.host, hpost, ?_⟩
  simp only [run]
  rcases runAttempt_wnear cfg size method ctx storage (fuelFor cfg wNearModule ctx) i hlimit hmin hmax
    hname hexp hft h1 h2 with ⟨e, he, hrun⟩ | ⟨-, hrun⟩
  · left
    rw [hrun]
    apply gasFailureUpTo_checkReceipts
    exact ⟨e, NearLogic.applyCharges_error h0 _ he, rfl, rfl, rfl, List.nil_prefix⟩
  rw [hrun]
  have hlogs' : logsOf s'.host = logsOf (erase s'.host) := rfl
  have hb := method_below cfg (F0 + wFuel cfg.wasm C) hl h1 h2 C (by omega) (by omega)
  simp only at hb
  rw [hlo, hs'] at hb
  rcases hb with ⟨hge, hlg, -, hisT⟩ | hrel
  · left
    apply gasFailureUpTo_checkReceipts
    have hl0 : hl.lastExecutionIssue = none := (erase_field he1 NearState.lastExecutionIssue fun _ => rfl).trans rfl
    have hi : (runInitialized cfg.wasm F0 (.next (startW cfg hl i))).1.host.lastExecutionIssue = none := by
      rw [hisT r' s' rfl (by rw [hl0]; exact (hend _ hpost).2)]
      exact hl0
    obtain ⟨e, he, ha, hrd, hrec, hl'⟩ := outcome_gasEndL ctx storage _ hge hi
    refine ⟨e, he, ha, hrd, hrec, ?_⟩
    rw [hl', ← hlogs']
    exact hlg.map _
  · right
    generalize hA : runInitialized cfg.wasm F0 (.next (startW cfg hl i)) = A at hrel ⊢
    obtain ⟨mc, err⟩ := A
    simp only [Prod.mk.injEq] at hrel
    obtain ⟨hm, rfl⟩ := hrel
    cases mc with
    | next c => simp [StepResult.relax] at hm
    | done vs s => simp [StepResult.relax] at hm
    | trap r s =>
      simp only [StepResult.relax, StepResult.trap.injEq] at hm
      obtain ⟨hr, hs⟩ := hm
      have hp' := hend _ hpost
      rw [hs] at hp'
      have hpp : FailureHost error (erase s.host) := hp'
      obtain ⟨hpo, -⟩ := outcome_failure ctx storage r s hpp
      obtain ⟨a1, a2, a3, a4⟩ := hpo
      exact ⟨a1, a2, a3, by rw [a4, hs]; rfl⟩


/-- Recorded protocol host failures preserve exact boundary errors and roll back, with no execution issue. -/
theorem observe_failure (ctx : Context) (raw : RawStorage)
    (codeOf : List UInt8 → Near.ContractCode) (o : VMOutcome) (error : HostError) (e : NearState)
    (ho : FailureOutcome o error e) (hi : FunctionCallError.issue? (.hostError error) = none) :
    let r := observeW ctx raw codeOf o
    r.outcome = .error (Near.Boundary.failureOf (.hostError error)) ∧
      RolledBack ctx raw r ∧ r.logs = logsOf e ∧
      ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  obtain ⟨ha, -, -, hl⟩ := ho
  have hout : (observeW ctx raw codeOf o).outcome =
      .error (Near.Boundary.failureOf (.hostError error)) := by
    simp only [observeW, Near.Boundary.observe, ha]
  refine ⟨hout, ?_, ?_, ?_⟩
  · have hrb := Near.Boundary.observe_rolledBack ctx raw.toList o _ _ hout
    rw [Finset.toList_toFinset] at hrb
    exact hrb
  · simp only [observeW, Near.Boundary.observe, ha]
    exact hl
  · intro msg hbad
    rw [hout] at hbad
    have hf : Near.Boundary.failureOf (.hostError error) ≠ .executionIssue msg := by
      unfold Near.Boundary.failureOf
      rw [hi]
      dsimp only
      split <;> simp
    exact hf (Except.error.inj hbad)

/-- Total recorded-failure run safety composes to the original full-context receipt observation. -/
theorem method_boundary_no_issue (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (error : HostError) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : RecordedFailureRun ctx.protocol i Pre cost Post) (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hendP : ∀ e, Post (eraseP (hostOf ctx raw)) e → FailureHost error e)
    (hi : FunctionCallError.issue? (.hostError error) = none) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    RolledBack ctx raw r ∧ ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  have hpos : 0 < minOpCost ctx.protocol.wasm := Nat.lt_min.mpr hwf.opCost_pos
  simp only [execOn_wCode]
  obtain ⟨e, hpost, hany⟩ := method_vm_anyFailure ctx.protocol size ctx.method (Near.Boundary.toVMContext ctx)
    raw.toList Pre cost Post error hpos hp.limit hp.pagesMin hp.pagesMax hname hexp hft h1 h2 hspec hpreP hendP
  rcases hany with hg | he
  · obtain ⟨-, hrb, -, hno⟩ := observe_gasFailure ctx raw codeOf _ _ hg
    exact ⟨hrb, hno⟩
  · obtain ⟨-, hrb, -, hno⟩ := observe_failure ctx raw codeOf _ error e he hi
    exact ⟨hrb, hno⟩

end WNear.Binary.RecordedFailure
