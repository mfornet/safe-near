import Bridge.Methods.Relational

/-!
# A method that panics, from its run to `Refines`

`Bridge/Methods/Relational.lean` for a run that ends in a trap after the host recorded a
`GuestPanic` (`env::panic_str` through `panic_utf8`): `MethodPanicsR` asks the run to end in a
trap with a final host `Post` relates to the initial one, and every such host to hold
`GuestPanic m` as its last error with no execution issue (`PanicHost`). The boundary observes
`Failure.panic m`, rolled back, with the host's logs (`observe_panic`), and the clauses of
`Refines` hold for a model step that fails with that panic and those logs (`AgreesPanic`).
-/

namespace WNear.Binary

open Wasm Wasm.Near NearLogic NearInterface ContractModel

/-- A host that panicked with `m`: its last error, and no execution issue. -/
def PanicHost (m : String) (e : NearState) : Prop :=
  e.lastError = some (.guestPanic m) ∧ e.lastExecutionIssue = none

/-- **The method's run ends in a panic.** From any host `h` with `Pre (erase h)`, room for
`cost (erase h)` within `Cg` and limits at least `Cg`, function `i` run from `startW` ends,
unless it exhausts its fuel, with a trap, a final host `Post` relates to `h` (both up to gas),
and at most `Cg` used. -/
def MethodPanicsR (cfg : RuntimeConfig) (i : Nat) (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) : Prop :=
  ∀ (fuel : Nat) (h : NearState) (Cg : Nat), Pre (erase h) → h.gas.used + cost (erase h) ≤ Cg →
    Cg ≤ h.gas.maxBurnt → Cg ≤ h.gas.prepaid →
    (runInitialized cfg.wasm fuel (.next (startW cfg h i))).2 ≠ some (.executionIssue .fuelExhausted) →
    ∃ r s, runInitialized cfg.wasm fuel (.next (startW cfg h i)) = (.trap r s, none) ∧
      Post (erase h) (erase s.host) ∧ s.host.gas.used ≤ Cg

/-- A VM outcome of a panic with `m` and the host `e`'s logs. -/
def PanicOutcome (o : VMOutcome) (m : String) (e : NearState) : Prop :=
  o.aborted = some (.hostError (.guestPanic m)) ∧ o.returnData = .none ∧ o.receipts = [] ∧
    o.logs = logsOf e

/-- A run that trapped after a panic. -/
theorem outcome_panic (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (r : Trap)
    (s : Store NearState) {m : String} (hp : PanicHost m (erase s.host)) :
    let o := (outcomeOfExecution ctx storage (.trap r s) none).checkReceipts ctx.accountBalance
      ctx.storageUsage storage
    PanicOutcome o m s.host ∧ o.burntGas = s.host.gas.burnt := by
  obtain ⟨he, hi⟩ := hp
  have he' : s.host.lastError = some (.guestPanic m) := he
  have hi' : s.host.lastExecutionIssue = none := hi
  have ht : trapError r s.host = .hostError (.guestPanic m) := by simp [trapError, hi', he']
  have hs : (StepResult.trap r s).host = s.host := rfl
  rw [checkReceipts_noReceipts _ _ _ _ (by simp [outcomeOfExecution, hs, ht])
    (by simp [outcomeOfExecution, hs, ht])]
  simp [outcomeOfExecution, hs, ht, PanicOutcome]

theorem gasUsed_burnt (g : Near.GasCounter) : g.burnt ≤ g.used := by
  simp [Near.GasCounter.used]

/-- **Enough gas, at the VM**: `run` panics as a host `Post` allows says. -/
theorem method_vmOutcomeP (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (m : String) (Cg : Nat)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodPanicsR cfg i Pre cost Post) (hpre : Pre (erase (ctx.toNearState cfg storage)))
    (hend : ∀ e, Post (erase (ctx.toNearState cfg storage)) e → PanicHost m e)
    (hgas : (ctx.toNearState cfg storage).gas.used +
      chargesUse (ctx.toNearState cfg storage) (loadingCharges size) +
        cost (erase (ctx.toNearState cfg storage)) ≤ Cg)
    (hC1 : Cg ≤ (ctx.toNearState cfg storage).gas.maxBurnt)
    (hC2 : Cg ≤ (ctx.toNearState cfg storage).gas.prepaid) :
    let o := run cfg wNearModule size method ctx storage
    ∃ e, Post (erase (ctx.toNearState cfg storage)) e ∧ PanicOutcome o m e ∧ o.burntGas ≤ Cg := by
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
  obtain ⟨hpo, hu⟩ := outcome_panic ctx storage r s (hend _ hpost)
  refine ⟨erase s.host, hpost, ?_⟩
  simp only [run]
  rw [hrun, hs]
  refine ⟨hpo, ?_⟩
  rw [hu]
  exact Nat.le_trans (gasUsed_burnt _) hused

/-- **Any gas, at the VM**: a gas or recorded-proof failure, or the panic. Only the run with the
limits raised, which records no proof, needs `Pre`. -/
theorem method_vm_anyP (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (m : String)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodPanicsR cfg i Pre cost Post) (hpre : Pre (eraseP (ctx.toNearState cfg storage)))
    (hend : ∀ e, Post (eraseP (ctx.toNearState cfg storage)) e → PanicHost m e) :
    let o := run cfg wNearModule size method ctx storage
    ∃ e, Post (eraseP (ctx.toNearState cfg storage)) e ∧
      (GasFailureUpTo o (logsOf e) ∨ PanicOutcome o m e) := by
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
      have hpp : PanicHost m (erase s.host) := hp'
      obtain ⟨hpo, -⟩ := outcome_panic ctx storage r s hpp
      obtain ⟨a1, a2, a3, a4⟩ := hpo
      exact ⟨a1, a2, a3, by rw [a4, hs]; rfl⟩

/-! ## The boundary -/

/-- A model step agreeing with a panic `m` from the host `e`: a failure that is that panic,
with `e`'s logs. -/
def AgreesPanic (M : ContractModel) (m : String) (e : NearState)
    (res : StepResult M.Panic M.State M.Ret M.Promise) : Prop :=
  ∃ f, res = .error f ∧ ModelFailure.toFailure M f.failure = .panic m ∧ f.logs = logsOf e

/-- A panic is observed as `Failure.panic`, rolled back, with the host's logs. -/
theorem observe_panic (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (codeOf : List UInt8 → Near.ContractCode) (o : VMOutcome) (m : String) (e : NearState)
    (ho : PanicOutcome o m e) (res : StepResult M.Panic M.State M.Ret M.Promise)
    (hag : AgreesPanic M m e res) :
    let r := observeW ctx raw codeOf o
    Matches M ctx raw r res ∧ r.usedGas = o.burntGas ∧ ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  obtain ⟨ha, -, -, hl⟩ := ho
  obtain ⟨f, rfl, hf, hfl⟩ := hag
  have hout : (observeW ctx raw codeOf o).outcome = .error (.panic m) := by
    simp only [observeW, Near.Boundary.observe, ha]
    rfl
  refine ⟨⟨by rw [hout, hf], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [observeW, Near.Boundary.observe, ha]
    exact Finset.toList_toFinset raw
  · simp only [observeW, Near.Boundary.observe, ha]
  · simp only [observeW, Near.Boundary.observe, ha]
  · simp only [observeW, Near.Boundary.observe, ha]
    rw [hl, hfl]
  · simp only [observeW, Near.Boundary.observe, ha]
  · simp only [observeW, Near.Boundary.observe, ha]
  · intro msg h
    rw [hout] at h
    cases h

/-- **The boundary for a method that panics**: no execution issue; with the host's
precondition and enough gas, the model's failing step, using at most `Cg`; under any gas and
any recorded proof, that step or a resource failure that rolls back with a prefix of its logs. -/
theorem method_boundaryP (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (m : String) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodPanicsR ctx.protocol i Pre cost Post) (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hend : ∀ e, Post (erase (hostOf ctx raw)) e → PanicHost m e)
    (hendP : ∀ e, Post (eraseP (hostOf ctx raw)) e → PanicHost m e)
    (res : StepResult M.Panic M.State M.Ret M.Promise)
    (hag : ∀ e, Post (erase (hostOf ctx raw)) e → AgreesPanic M m e res)
    (hagP : ∀ e, Post (eraseP (hostOf ctx raw)) e → AgreesPanic M m e res) (Cg : Nat) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (Pre (erase (hostOf ctx raw)) →
      chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ Cg →
      Cg ≤ ctx.gasLimit → Matches M ctx raw r res ∧ r.usedGas ≤ Cg) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hpos : 0 < minOpCost ctx.protocol.wasm := Nat.lt_min.mpr hwf.opCost_pos
  simp only [execOn_wCode]
  obtain ⟨e0, hpost0, hany⟩ := method_vm_anyP ctx.protocol size ctx.method (Near.Boundary.toVMContext ctx)
    raw.toList Pre cost Post m hpos hp.limit hp.pagesMin hp.pagesMax hname hexp hft h1 h2 hspec hpreP hendP
  have hlogs : res.logs = logsOf e0 := by
    obtain ⟨f, rfl, -, hfl⟩ := hagP e0 hpost0
    exact hfl
  refine ⟨?_, ?_, ?_⟩
  · rcases hany with hg | he
    · exact (observe_gasFailure ctx raw codeOf _ _ hg).2.2.2
    · exact (observe_panic M ctx raw codeOf _ m e0 he res (hagP e0 hpost0)).2.2
  · intro hpre hgas hlim
    have hused0 : (hostOf ctx raw).gas.used = 0 := rfl
    have hmb : (hostOf ctx raw).gas.maxBurnt = ctx.protocol.wasm.limits.maxGasBurnt := rfl
    have hpp : (hostOf ctx raw).gas.prepaid = ctx.prepaidGas := rfl
    obtain ⟨e1, hpost1, heff, hu⟩ := method_vmOutcomeP ctx.protocol size ctx.method
      (Near.Boundary.toVMContext ctx) raw.toList Pre cost Post m Cg hpos hp.limit hp.pagesMin hp.pagesMax hname
      hexp hft h1 h2 hspec hpre hend
      (by show 0 + chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ Cg; omega)
      (by show Cg ≤ (hostOf ctx raw).gas.maxBurnt; rw [hmb]; exact Nat.le_trans hlim (Nat.min_le_right _ _))
      (by show Cg ≤ (hostOf ctx raw).gas.prepaid; rw [hpp]; exact Nat.le_trans hlim (Nat.min_le_left _ _))
    obtain ⟨hm, hug, -⟩ := observe_panic M ctx raw codeOf _ m e1 heff res (hag e1 hpost1)
    refine ⟨hm, ?_⟩
    rw [hug]
    exact hu
  · rcases hany with hg | he
    · right
      obtain ⟨ho, hrb, hl, -⟩ := observe_gasFailure ctx raw codeOf _ _ hg
      exact ⟨ho, hrb, by rw [hlogs]; exact hl⟩
    · left
      exact (observe_panic M ctx raw codeOf _ m e0 he res (hagP e0 hpost0)).1

/-- **The clauses of `Refines` for a call to a method that panics.** -/
theorem method_refines_callP (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option M.State) (ctx : Context) (c : M.Call) {i : Nat}
    (Pre : NearState → Prop) (cost : NearState → Nat) (Post : NearState → NearState → Prop) (m : String)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodPanicsR ctx.protocol i Pre cost Post)
    (hpre : ctx.ProofRoom (M.proofBound ctx st c) → Pre (erase (hostOf ctx raw)))
    (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hend : ∀ e, Post (erase (hostOf ctx raw)) e → PanicHost m e)
    (hendP : ∀ e, Post (eraseP (hostOf ctx raw)) e → PanicHost m e)
    (hag : ∀ e, Post (erase (hostOf ctx raw)) e → AgreesPanic M m e (M.step ctx st c))
    (hagP : ∀ e, Post (eraseP (hostOf ctx raw)) e → AgreesPanic M m e (M.step ctx st c))
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ M.gas ctx st c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := M.step ctx st c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (M.gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom (M.proofBound ctx st c) →
      Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hni, hen, hany⟩ := method_boundaryP M size codeOf raw ctx Pre cost Post m hp hwf hname hexp hft h1 h2
    hspec hpreP hend hendP (M.step ctx st c) hag hagP (M.gas ctx st c)
  exact ⟨hni, fun hgas hroom => hen (hpre hroom) hbound hgas, hany⟩

end WNear.Binary
