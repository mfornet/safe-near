import Bridge.Method

/-!
# A method's run, up to a relation on the host

`Bridge/Method.lean`'s `MethodRuns cfg i Pre cost F` asks the final host to be `F` of the
initial one, up to gas. A method that reads storage cannot meet it: `storage_read` leaves the
value in register 0 and updates the accounting's caches (`StorageReadPost`: some `s2` with the
same data), which no function of the initial host pins down. `MethodRunsR` relaxes `F` to a
relation `Post` between the initial host and the final one (both up to gas), and
`method_refines_callR` is `method_refines_call` for it: the model's step must agree with every
host `Post` allows (`AgreesWith` only reads the return data, storage, balance, usage and logs).

`methodRunsR_of` embeds `MethodRuns` (`Post e e' := e' = erase (F e)`).
-/

namespace WNear.Binary

open Wasm Wasm.Near NearLogic NearInterface ContractModel

/-- **The method's run, up to a relation.** From any host `h` with `Pre (erase h)`, room for
`cost (erase h)` within `Cg` and limits at least `Cg`, function `i` run from `startW` ends,
unless it exhausts its fuel, with no values, a final host `Post` relates to `h` (both up to
gas), and at most `Cg` used. -/
def MethodRunsR (cfg : RuntimeConfig) (i : Nat) (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) : Prop :=
  ∀ (fuel : Nat) (h : NearState) (Cg : Nat), Pre (erase h) → h.gas.used + cost (erase h) ≤ Cg →
    Cg ≤ h.gas.maxBurnt → Cg ≤ h.gas.prepaid →
    (runInitialized cfg.wasm fuel (.next (startW cfg h i))).2 ≠ some (.executionIssue .fuelExhausted) →
    ∃ s, runInitialized cfg.wasm fuel (.next (startW cfg h i)) = (.done [] s, none) ∧
      Post (erase h) (erase s.host) ∧ s.host.gas.used ≤ Cg

theorem erase_erase (h : NearState) : erase (erase h) = erase h := rfl

theorem methodRunsR_of {cfg : RuntimeConfig} {i : Nat} {Pre : NearState → Prop} {cost : NearState → Nat}
    {F : NearState → NearState} (hF : MethodRuns cfg i Pre cost F) :
    MethodRunsR cfg i Pre cost (fun e e' => e' = erase (F e)) := by
  intro fuel h Cg hp hc h1 h2 hfu
  obtain ⟨s, hs, he, hu⟩ := hF fuel h Cg hp hc h1 h2 hfu
  exact ⟨s, hs, he, hu⟩

/-- **Enough gas, at the VM**, up to a relation: `run` has the effects of a host `Post` allows. -/
theorem method_vmOutcomeR (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (Cg : Nat)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRunsR cfg i Pre cost Post) (hpre : Pre (erase (ctx.toNearState cfg storage)))
    (hnp : ∀ e, Post (erase (ctx.toNearState cfg storage)) e → NoPromises e)
    (hgas : (ctx.toNearState cfg storage).gas.used +
      chargesUse (ctx.toNearState cfg storage) (loadingCharges size) +
        cost (erase (ctx.toNearState cfg storage)) ≤ Cg)
    (hC1 : Cg ≤ (ctx.toNearState cfg storage).gas.maxBurnt)
    (hC2 : Cg ≤ (ctx.toNearState cfg storage).gas.prepaid) :
    let o := run cfg wNearModule size method ctx storage
    ∃ e, Post (erase (ctx.toNearState cfg storage)) e ∧ Effects o e ∧ o.usedGas ≤ Cg ∧
      o.burntGas ≤ o.usedGas := by
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
  obtain ⟨s, hs, hpost, hused⟩ := hspec (fuelFor cfg wNearModule ctx) hl Cg (by rw [he1]; exact hpre)
    (by rw [he1, hch.used]; omega) (by rw [hch.maxBurnt]; exact hC1) (by rw [hch.prepaid]; exact hC2) hfuel
  rw [he1] at hpost
  obtain ⟨heff, hu, hb⟩ := outcome_done ctx storage s (erase s.host) rfl (hnp _ hpost)
  refine ⟨erase s.host, hpost, ?_⟩
  simp only [run]
  rw [hrun, hs]
  exact ⟨heff, by rw [hu]; exact hused, hb⟩

/-- **Any gas, at the VM**, up to a relation. Only the run with the limits raised, which records no
proof, needs `Pre`, from the host without its recorded proof. -/
theorem method_vm_anyR (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRunsR cfg i Pre cost Post) (hpre : Pre (eraseP (ctx.toNearState cfg storage)))
    (hnp : ∀ e, Post (eraseP (ctx.toNearState cfg storage)) e → NoPromises e) :
    let o := run cfg wNearModule size method ctx storage
    ∃ e, Post (eraseP (ctx.toNearState cfg storage)) e ∧ (GasFailureUpTo o (logsOf e) ∨ Effects o e) := by
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
  obtain ⟨s', hs', hpost', -⟩ := hspec (F0 + wFuel cfg.wasm C) (relax hl C C) C
    (by show Pre (eraseP hl); rw [eraseP_of_erase he1]; exact hpre)
    (by show hl.gas.used + cost (eraseP hl) ≤ C; rw [eraseP_of_erase he1]; omega) (Nat.le_refl _) (Nat.le_refl _) hfuelHi
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
  rcases hb with ⟨hge, hlg, hiss⟩ | hrel
  · left
    apply gasFailureUpTo_checkReceipts
    have hi : (runInitialized cfg.wasm F0 (.next (startW cfg hl i))).1.host.lastExecutionIssue = none := by
      rw [hiss ⟨[], s', rfl⟩]
      exact (erase_field he1 NearState.lastExecutionIssue fun _ => rfl).trans rfl
    obtain ⟨e, he, ha, hrd, hrec, hl'⟩ := outcome_gasEndL ctx storage _ hge hi
    refine ⟨e, he, ha, hrd, hrec, ?_⟩
    rw [hl', ← hlogs']
    exact hlg.map _
  · right
    generalize hA : runInitialized cfg.wasm F0 (.next (startW cfg hl i)) = A at hrel ⊢
    obtain ⟨m, err⟩ := A
    simp only [Prod.mk.injEq] at hrel
    obtain ⟨hm, rfl⟩ := hrel
    cases m with
    | next c => simp [StepResult.relax] at hm
    | trap r s => simp [StepResult.relax] at hm
    | done vs s =>
      simp only [StepResult.relax, StepResult.done.injEq] at hm
      obtain ⟨rfl, hs⟩ := hm
      have he : eraseP s.host = eraseP (erase s'.host) := by
        rw [hs]; rfl
      exact (outcome_done ctx storage s _ he (hnp _ hpost)).1

/-- **The boundary**, up to a relation: the clauses of `method_boundary` for a model step that
agrees with every final host `Post` allows, from the host as it is (enough resources, under
`Pre`) and from the host without its recorded proof (any resources). -/
theorem method_boundaryR (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (Post : NearState → NearState → Prop) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRunsR ctx.protocol i Pre cost Post) (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hnp : ∀ e, Post (erase (hostOf ctx raw)) e → NoPromises e)
    (hnpP : ∀ e, Post (eraseP (hostOf ctx raw)) e → NoPromises e)
    (res : StepResult M.Panic M.State M.Ret M.Promise)
    (hag : ∀ e, Post (erase (hostOf ctx raw)) e → AgreesWith M ctx raw e res)
    (hagP : ∀ e, Post (eraseP (hostOf ctx raw)) e → AgreesWith M ctx raw e res) (Cg : Nat) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (Pre (erase (hostOf ctx raw)) →
      chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ Cg →
      Cg ≤ ctx.gasLimit → Matches M ctx raw r res ∧ r.usedGas ≤ Cg) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hpos : 0 < minOpCost ctx.protocol.wasm := Nat.lt_min.mpr hwf.opCost_pos
  simp only [execOn_wCode]
  obtain ⟨e0, hpost0, hany⟩ := method_vm_anyR ctx.protocol size ctx.method (Near.Boundary.toVMContext ctx)
    raw.toList Pre cost Post hpos hp.limit hp.pagesMin hp.pagesMax hname hexp hft h1 h2 hspec hpreP hnpP
  have hlogs := (hagP e0 hpost0).logs
  refine ⟨?_, ?_, ?_⟩
  · rcases hany with hg | he
    · exact (observe_gasFailure ctx raw codeOf _ _ hg).2.2.2
    · exact (observe_effects M ctx raw codeOf _ _ he res (hagP e0 hpost0)).2.2
  · intro hpre hgas hlim
    have hused0 : (hostOf ctx raw).gas.used = 0 := rfl
    have hmb : (hostOf ctx raw).gas.maxBurnt = ctx.protocol.wasm.limits.maxGasBurnt := rfl
    have hpp : (hostOf ctx raw).gas.prepaid = ctx.prepaidGas := rfl
    obtain ⟨e1, hpost1, heff, hu, hbu⟩ := method_vmOutcomeR ctx.protocol size ctx.method
      (Near.Boundary.toVMContext ctx) raw.toList Pre cost Post Cg hpos hp.limit hp.pagesMin hp.pagesMax hname
      hexp hft h1 h2 hspec hpre hnp
      (by show 0 + chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ Cg; omega)
      (by show Cg ≤ (hostOf ctx raw).gas.maxBurnt; rw [hmb]; exact Nat.le_trans hlim (Nat.min_le_right _ _))
      (by show Cg ≤ (hostOf ctx raw).gas.prepaid; rw [hpp]; exact Nat.le_trans hlim (Nat.min_le_left _ _))
    obtain ⟨hm, hug, -⟩ := observe_effects M ctx raw codeOf _ _ heff res (hag e1 hpost1)
    refine ⟨hm, ?_⟩
    rcases hug with h | h
    · rw [h]; exact hu
    · rw [h]; exact Nat.le_trans hbu hu
  · rcases hany with hg | he
    · right
      obtain ⟨ho, hrb, hl, -⟩ := observe_gasFailure ctx raw codeOf _ _ hg
      exact ⟨ho, hrb, by rw [hlogs]; exact hl⟩
    · left
      exact (observe_effects M ctx raw codeOf _ _ he res (hagP e0 hpost0)).1

/-- **The clauses of `Refines` for a call to the method**, up to a relation. The host's
precondition may need room in the recorded proof for the model's bound. -/
theorem method_refines_callR (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option M.State) (ctx : Context) (c : M.Call) {i : Nat}
    (Pre : NearState → Prop) (cost : NearState → Nat) (Post : NearState → NearState → Prop)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRunsR ctx.protocol i Pre cost Post)
    (hpre : ctx.ProofRoom (M.proofBound ctx st c) → Pre (erase (hostOf ctx raw)))
    (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hnp : ∀ e, Post (erase (hostOf ctx raw)) e → NoPromises e)
    (hnpP : ∀ e, Post (eraseP (hostOf ctx raw)) e → NoPromises e)
    (hag : ∀ e, Post (erase (hostOf ctx raw)) e → AgreesWith M ctx raw e (M.step ctx st c))
    (hagP : ∀ e, Post (eraseP (hostOf ctx raw)) e → AgreesWith M ctx raw e (M.step ctx st c))
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ M.gas ctx st c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := M.step ctx st c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (M.gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom (M.proofBound ctx st c) →
      Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hni, hen, hany⟩ := method_boundaryR M size codeOf raw ctx Pre cost Post hp hwf hname hexp hft h1 h2
    hspec hpreP hnp hnpP (M.step ctx st c) hag hagP (M.gas ctx st c)
  exact ⟨hni, fun hgas hroom => hen (hpre hroom) hbound hgas, hany⟩

end WNear.Binary
