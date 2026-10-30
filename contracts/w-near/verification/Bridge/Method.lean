import Bridge.Below
import NearLogic
import NearRuntime.Boundary
import NearRuntime.BoundaryResolution

/-!
# A method of `contract.wasm`, from its run to `Refines`

The wNEAR analogue of the walking skeleton's chain (`get_run`,
`get_vmOutcome`, `get_vm_any`, `get_boundary`), for any exported function
`i` of type `[] → []`, generic in what the method does to the host.

What a method does is the hypothesis `MethodRuns cfg i Pre cost F`: from any
host after loading satisfying `Pre` (read up to gas), with room for `cost`
within `Cg`, a run that does not exhaust its fuel ends with no values, the
host as `F` says up to gas, and at most `Cg` used. `Pre`, `cost` and `F` read
the host through `erase`, so they are blind to gas, as raising the limits
needs. Only methods that create no promises (`NoPromises`) are covered.

* `method_fuel`: `run`'s default fuel is enough for any method.
* `method_vmOutcome`: with enough gas, `run`'s outcome is read from `F`.
* `method_vm_any`: under any gas and any recorded proof, the same outcome or a
  resource failure (gas, or the recorded proof) whose logs are a prefix of
  `F`'s. It needs `Pre` only of the host recording no proof (`eraseP`), as
  the run with raised limits records none.
* `method_boundary`: both, through `Near.Boundary.execOn`, as the clauses
  of `Refines` for a model step agreeing with `F` (`AgreesWith`).
-/

namespace WNear.Binary

open Wasm Wasm.Near NearLogic NearInterface ContractModel

/-! ## Fuel -/

theorem moduleBody_wPrepared : moduleBody wPrepared = moduleBody wNearModule := by
  unfold moduleBody; rfl

theorem startW_host (cfg : RuntimeConfig) (h : NearState) (i : Nat) : (startW cfg h i).store.host = h := rfl

theorem startW_fuelInv (cfg : RuntimeConfig) (h : NearState) {i : Nat} (h1 : 48 ≤ i) (h2 : i < 955)
    {p m : Nat} (hf : GasFloor 0 p m h) : FuelInv p m (startW cfg h i) := by
  obtain ⟨vm, -, hvm⟩ := validate_wPrepared
  exact ⟨startWasm_bounded (startWasm_wStore cfg h h1 h2),
    resolved_floorHosts (resolve_wPrepared cfg) (allocate_wHosts cfg h) (instantiate_wPrepared cfg h vm hvm), hf⟩

theorem startW_span (cfg : RuntimeConfig) (h : NearState) (i : Nat) :
    span (startW cfg h i) ≤ max 1 execLimits.maxCallDepth * (moduleBody wNearModule + 1) := by
  obtain ⟨vm, -, hvm⟩ := validate_wPrepared
  have hb := resolved_maxBody (allocate_wHosts cfg h) (instantiate_wPrepared cfg h vm hvm)
  rw [hvm, moduleBody_wPrepared] at hb
  show max 1 execLimits.maxCallDepth * (Exec.maxBody (wStore cfg h) + 1) ≤ _
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hb 1)

/-- Fuel enough for any run of `contract.wasm` under the burn limit `m`. -/
noncomputable def wFuel (cfg : WasmConfig) (m : Nat) : Nat :=
  (m / minOpCost cfg + 1) * (max 1 execLimits.maxCallDepth * (moduleBody wNearModule + 1) + 1)

theorem fuelFor_wNear (cfg : RuntimeConfig) (ctx : VMContext) :
    fuelFor cfg wNearModule ctx = wFuel cfg.wasm (ctx.maxBurnt cfg) := rfl

/-- From a host within limits `p`, `m`, a method with `wFuel m` fuel never
stops for want of fuel. -/
theorem startW_enough_fuel (cfg : RuntimeConfig) (h : NearState) {i : Nat} (h1 : 48 ≤ i) (h2 : i < 955)
    {p m : Nat} (hf : GasFloor 0 p m h) (hpos : 0 < minOpCost cfg.wasm) {fuel : Nat}
    (hfuel : wFuel cfg.wasm m ≤ fuel) :
    (runInitialized cfg.wasm fuel (.next (startW cfg h i))).2 ≠ some (.executionIssue .fuelExhausted) :=
  runInitialized_enough_fuel hpos (startW_fuelInv cfg h h1 h2 hf)
    (Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (startW_span cfg h i) 1)) hfuel)

theorem toNearState_floor (cfg : RuntimeConfig) (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) :
    GasFloor 0 ctx.prepaidGas (ctx.maxBurnt cfg) (ctx.toNearState cfg storage) := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl, ?_⟩
  unfold VMContext.toNearState VMContext.maxBurnt
  cases ctx.viewConfig <;> rfl

/-- The host after loading, within the context's limits. -/
theorem loaded_floor (cfg : RuntimeConfig) (size : Nat) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) :
    GasFloor 0 ctx.prepaidGas (ctx.maxBurnt cfg)
      (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1 :=
  applyCharges_floor _ _ (toNearState_floor cfg ctx storage)

/-- **Fuel.** With `run`'s default fuel, no method of `contract.wasm` stops
for want of fuel. -/
theorem method_fuel (cfg : RuntimeConfig) (size : Nat) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (h1 : 48 ≤ i) (h2 : i < 955)
    (hpos : 0 < minOpCost cfg.wasm) :
    (runInitialized cfg.wasm (fuelFor cfg wNearModule ctx)
      (.next (startW cfg (applyCharges (ctx.toNearState cfg storage) (loadingCharges size)).1 i))).2 ≠
      some (.executionIssue .fuelExhausted) :=
  startW_enough_fuel cfg _ h1 h2 (loaded_floor cfg size ctx storage) hpos (Nat.le_refl _)

/-! ## What a method does -/

/-- **The method's run.** From any host `h` with `Pre (erase h)`, room for
`cost (erase h)` within `Cg` and limits at least `Cg`, function `i` run from
`startW` ends, unless it exhausts its fuel, with no values, the host as
`F (erase h)` up to gas, and at most `Cg` used. -/
def MethodRuns (cfg : RuntimeConfig) (i : Nat) (Pre : NearState → Prop) (cost : NearState → Nat)
    (F : NearState → NearState) : Prop :=
  ∀ (fuel : Nat) (h : NearState) (Cg : Nat), Pre (erase h) → h.gas.used + cost (erase h) ≤ Cg →
    Cg ≤ h.gas.maxBurnt → Cg ≤ h.gas.prepaid →
    (runInitialized cfg.wasm fuel (.next (startW cfg h i))).2 ≠ some (.executionIssue .fuelExhausted) →
    ∃ s, runInitialized cfg.wasm fuel (.next (startW cfg h i)) = (.done [] s, none) ∧
      erase s.host = erase (F (erase h)) ∧ s.host.gas.used ≤ Cg

/-- A host that created no promises and selected none as its result. -/
structure NoPromises (e : NearState) : Prop where
  promises : e.promises = []
  returned : e.returnedPromise = none
  weights : e.gasWeights = []

/-- The return data a host has selected. -/
def returnOf (e : NearState) : ReturnData :=
  match e.returnData with
  | some b => .value b
  | none => .none

/-- A VM outcome with the effects of the host `e`: no abort, no receipts, and
return data, logs, balance, usage and storage as `e` has them. -/
def Effects (o : VMOutcome) (e : NearState) : Prop :=
  o.aborted = none ∧ o.returnData = returnOf e ∧ o.receipts = [] ∧ o.distributedGas = 0 ∧
    o.logs = logsOf e ∧ o.balance = e.context.accountBalance ∧
    o.storageUsage = e.context.storageUsage.toNat ∧ o.storage = finalStorage e

/-- A gas failure whose logs are a prefix of `logs`. -/
def GasFailureUpTo (o : VMOutcome) (logs : List String) : Prop :=
  ∃ e, isGasError e ∧ o.aborted = some (.hostError e) ∧ o.returnData = .none ∧ o.receipts = [] ∧
    o.logs <+: logs

theorem gasFailureUpTo_checkReceipts {o : VMOutcome} {logs : List String} (h : GasFailureUpTo o logs)
    (balance usage : Nat) (storage : List (List UInt8 × List UInt8)) :
    GasFailureUpTo (o.checkReceipts balance usage storage) logs := by
  obtain ⟨e, he, ha, hrd, hr, hl⟩ := h
  rw [checkReceipts_noReceipts o balance usage storage hr (by rw [hrd]; intro i; simp)]
  exact ⟨e, he, ha, hrd, hr, hl⟩

/-- A run done with the host `e`, up to gas and the recorded proof, and no promises. -/
theorem outcome_done (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (s : Store NearState)
    (e : NearState) (he : eraseP s.host = eraseP e) (hn : NoPromises e) :
    let o := (outcomeOfExecution ctx storage (.done [] s) none).checkReceipts ctx.accountBalance
      ctx.storageUsage storage
    Effects o e ∧ o.usedGas = s.host.gas.used ∧ o.burntGas ≤ o.usedGas := by
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (eraseP x) = f x) → f s.host = f e :=
    fun f hfe => eraseP_field he f hfe
  have hp : s.host.promises = [] := (hf NearState.promises fun _ => rfl).trans hn.promises
  have hr : s.host.returnedPromise = none := (hf NearState.returnedPromise fun _ => rfl).trans hn.returned
  have hw : s.host.gasWeights = [] := (hf NearState.gasWeights fun _ => rfl).trans hn.weights
  obtain ⟨ha, hrec, hret, husd, hbrn, hdist, hb, hu, hl, hs⟩ :=
    outcomeOfExecution_noPromises ctx storage [] s hp hr hw
  have hrd : s.host.returnData = e.returnData := hf NearState.returnData fun _ => rfl
  rw [checkReceipts_noReceipts _ _ _ _ hrec (by rw [hret]; intro i; split <;> simp)]
  refine ⟨⟨ha, ?_, hrec, hdist, ?_, ?_, ?_, ?_⟩, husd, ?_⟩
  · rw [hret, hrd]; rfl
  · rw [hl]; exact hf logsOf fun _ => rfl
  · rw [hb]; exact hf (fun x => x.context.accountBalance) fun _ => rfl
  · rw [hu]; exact hf (fun x => x.context.storageUsage.toNat) fun _ => rfl
  · rw [hs]; exact hf finalStorage fun _ => rfl
  · rw [hbrn, husd]; simp [Near.GasCounter.used]

/-! ## The VM outcome with enough gas -/

/-- **Enough gas, at the VM.** With room for loading and the method's cost
within `Cg`, `run` has the effects of `F` on the context's host and uses at
most `Cg`. -/
theorem method_vmOutcome (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (F : NearState → NearState) (Cg : Nat)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRuns cfg i Pre cost F) (hpre : Pre (erase (ctx.toNearState cfg storage)))
    (hnp : NoPromises (F (erase (ctx.toNearState cfg storage))))
    (hgas : (ctx.toNearState cfg storage).gas.used +
      chargesUse (ctx.toNearState cfg storage) (loadingCharges size) +
        cost (erase (ctx.toNearState cfg storage)) ≤ Cg)
    (hC1 : Cg ≤ (ctx.toNearState cfg storage).gas.maxBurnt)
    (hC2 : Cg ≤ (ctx.toNearState cfg storage).gas.prepaid) :
    let o := run cfg wNearModule size method ctx storage
    Effects o (F (erase (ctx.toNearState cfg storage))) ∧ o.usedGas ≤ Cg ∧ o.burntGas ≤ o.usedGas := by
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
  obtain ⟨s, hs, hhost, hused⟩ := hspec (fuelFor cfg wNearModule ctx) hl Cg (by rw [he1]; exact hpre)
    (by rw [he1, hch.used]; omega) (by rw [hch.maxBurnt]; exact hC1) (by rw [hch.prepaid]; exact hC2) hfuel
  rw [he1] at hhost
  obtain ⟨heff, hu, hb⟩ := outcome_done ctx storage s _ (eraseP_of_erase hhost) hnp
  simp only [run]
  rw [hrun, hs]
  exact ⟨heff, by rw [hu]; exact hused, hb⟩

/-! ## The VM outcome under any gas -/

/-- A run that ended with a gas failure, with its host's logs. -/
theorem outcome_gasEndL (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (r : Machine × Option FunctionCallError) (hg : GasEnd r) (hi : r.1.host.lastExecutionIssue = none) :
    ∃ e, isGasError e ∧ (outcomeOfExecution ctx storage r.1 r.2).aborted = some (.hostError e) ∧
      (outcomeOfExecution ctx storage r.1 r.2).returnData = .none ∧
      (outcomeOfExecution ctx storage r.1 r.2).receipts = [] ∧
      (outcomeOfExecution ctx storage r.1 r.2).logs = logsOf r.1.host := by
  obtain ⟨m, err⟩ := r
  rcases hg with ⟨e, he, hge⟩ | ⟨hn, reason, s, e, hm, hle, hge⟩
  · simp only at he hi
    subst he
    exact ⟨e, hge, rfl, rfl, rfl, rfl⟩
  · simp only at hn hm hi
    subst hn hm
    have ht : trapError reason s.host = .hostError e := by
      simp only [StepResult.host] at hi
      simp [trapError, hi, hle]
    have hs : (StepResult.trap reason s).host = s.host := rfl
    refine ⟨e, hge, ?_, rfl, rfl, ?_⟩
    · simp [outcomeOfExecution, hs, ht]
    · simp [outcomeOfExecution, hs, ht]

/-- **Any gas, at the VM.** The call fails for gas or for the recorded
proof, with logs a prefix of `F`'s, or it has the effects it has with enough
gas and no proof recorded. Only the run with the limits raised, which records
no proof, needs `Pre`. -/
theorem method_vm_any (cfg : RuntimeConfig) (size : Nat) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (F : NearState → NearState)
    (hpos : 0 < minOpCost cfg.wasm) (hlimit : prepareLimitError cfg.wasm.limits wNearModule = none)
    (hmin : cfg.wasm.limits.initialMemoryPages = 1024) (hmax : cfg.wasm.limits.maxMemoryPages = 2048)
    (hname : method.isEmpty = false) (hexp : wNearModule.exportFunc? method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRuns cfg i Pre cost F) (hpre : Pre (eraseP (ctx.toNearState cfg storage)))
    (hnp : NoPromises (F (eraseP (ctx.toNearState cfg storage)))) :
    let o := run cfg wNearModule size method ctx storage
    GasFailureUpTo o (logsOf (F (eraseP (ctx.toNearState cfg storage)))) ∨
      Effects o (F (eraseP (ctx.toNearState cfg storage))) := by
  set h0 := ctx.toNearState cfg storage
  set hl := (applyCharges h0 (loadingCharges size)).1
  have he1 : erase hl = erase h0 := applyCharges_erase h0 _
  simp only [run]
  rcases runAttempt_wnear cfg size method ctx storage (fuelFor cfg wNearModule ctx) i hlimit hmin hmax
    hname hexp hft h1 h2 with ⟨e, he, hrun⟩ | ⟨-, hrun⟩
  · left
    rw [hrun]
    apply gasFailureUpTo_checkReceipts
    exact ⟨e, NearLogic.applyCharges_error h0 _ he, rfl, rfl, rfl, List.nil_prefix⟩
  rw [hrun]
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
  obtain ⟨s', hs', hhost', -⟩ := hspec (F0 + wFuel cfg.wasm C) (relax hl C C) C
    (by show Pre (eraseP hl); rw [eraseP_of_erase he1]; exact hpre)
    (by show hl.gas.used + cost (eraseP hl) ≤ C; rw [eraseP_of_erase he1]; omega) (Nat.le_refl _) (Nat.le_refl _) hfuelHi
  have hhost : erase s'.host = erase (F (eraseP h0)) := by
    have : erase (relax hl C C) = eraseP hl := rfl
    rw [hhost', this, eraseP_of_erase he1]
  have hlogs' : logsOf s'.host = logsOf (F (eraseP h0)) := erase_field hhost logsOf fun _ => rfl
  have hb := method_below cfg (F0 + wFuel cfg.wasm C) hl h1 h2 C (by omega) (by omega)
  simp only at hb
  rw [hlo, hs'] at hb
  rcases hb with ⟨hge, hlg, hiss, -⟩ | hrel
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
      have he : eraseP s.host = eraseP (F (eraseP h0)) := by
        rw [← eraseP_of_erase hhost, hs]; rfl
      exact (outcome_done ctx storage s _ he hnp).1

/-! ## The boundary -/

/-- `contract.wasm`, deployed with `size` bytes, as the boundary runs it. -/
noncomputable def wCode (size : Nat) (codeOf : List UInt8 → Near.ContractCode) : Near.Boundary.Code :=
  { code := { module := wNearModule, size, hash := "" }, codeOf }

/-- What a method needs of the protocol config. -/
structure WProtocol (p : RuntimeConfig) : Prop where
  limit : prepareLimitError p.wasm.limits wNearModule = none
  pagesMin : p.wasm.limits.initialMemoryPages = 1024
  pagesMax : p.wasm.limits.maxMemoryPages = 2048

/-- The host a call starts from, before loading. -/
noncomputable def hostOf (ctx : Context) (raw : RawStorage) : NearState :=
  (Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw.toList

/-- A model step agreeing with the host `e` a call ends with: a success with
`e`'s return data, storage, balance, usage and logs and no receipts, when the
account can pay for its storage; the storage-stake failure, with `e`'s logs,
when it cannot. -/
def AgreesWith (M : ContractModel) (ctx : Context) (raw : RawStorage) (e : NearState) :
    StepResult M.Panic M.State M.Ret M.Promise → Prop
  | .ok o =>
    stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked = 0 ∧
    (∀ g, M.encodeReceipts g o.promises = []) ∧
    returnOf e = M.encodeRet o.ret ∧
    (finalStorage e).toFinset = M.encodeState o.state ∧
    e.context.accountBalance = ctx.balance + ctx.attached ∧
    e.context.storageUsage.toNat = ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (M.encodeState o.state) ∧
    logsOf e = o.logs
  | .error f =>
    0 < stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked ∧
    ModelFailure.toFailure M f.failure = .lackBalanceForState
      (stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked) ∧
    f.logs = logsOf e

theorem AgreesWith.logs {M : ContractModel} {ctx : Context} {raw : RawStorage} {e : NearState}
    {res : StepResult M.Panic M.State M.Ret M.Promise} (h : AgreesWith M ctx raw e res) :
    res.logs = logsOf e := by
  cases res with
  | ok o => exact h.2.2.2.2.2.2.symm
  | error f => exact h.2.2

/-- The boundary's observation of an outcome. -/
noncomputable def observeW (ctx : Context) (raw : RawStorage) (codeOf : List UInt8 → Near.ContractCode)
    (o : VMOutcome) : Observation :=
  Near.Boundary.observe ctx raw.toList o (Near.Boundary.actionsIssue? codeOf o.receipts)
    (match Near.checkVMReceipts ctx.protocol codeOf ctx.current ctx.signer ctx.signerPk o.receipts with
     | .error error => some (.newReceiptValidationError error)
     | .ok () => none)

theorem execOn_wCode (size : Nat) (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage)
    (ctx : Context) :
    Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx =
      observeW ctx raw codeOf (run ctx.protocol wNearModule size ctx.method (Near.Boundary.toVMContext ctx)
        raw.toList) := rfl

/-- An outcome with the effects of `e` is observed as a model step agreeing
with `e`. -/
theorem observe_effects (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (codeOf : List UInt8 → Near.ContractCode) (o : VMOutcome) (e : NearState) (heff : Effects o e)
    (res : StepResult M.Panic M.State M.Ret M.Promise) (hag : AgreesWith M ctx raw e res) :
    let r := observeW ctx raw codeOf o
    Matches M ctx raw r res ∧ (r.usedGas = o.usedGas ∨ r.usedGas = o.burntGas) ∧
      ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  obtain ⟨ha, hrd, hrec, hdist, hl, hb, hsu, hs⟩ := heff
  have hcheck : Near.checkVMReceipts ctx.protocol codeOf ctx.current ctx.signer ctx.signerPk [] =
      Except.ok () := rfl
  simp only [observeW, hrec, Near.Boundary.actionsIssue?, List.findSome?_nil, hcheck,
    Near.Boundary.observe, ha, hsu, hb]
  cases res with
  | ok out =>
    obtain ⟨hd, hrs, hret, hst, hbal, husage, hlogs⟩ := hag
    simp only [hd, gt_iff_lt, Nat.lt_irrefl, ite_false]
    refine ⟨⟨by rw [hrd, hret], by rw [hs, hst], ?_, husage, by rw [hl, hlogs], (hrs _).symm⟩,
      Or.inl (by rw [hdist, Nat.sub_zero]), ?_⟩
    · rw [hbal, hrs]; simp [receiptDeposits]
    · intro msg h; cases h
  | error f =>
    obtain ⟨hd, hfail, hlogs⟩ := hag
    simp only [gt_iff_lt, hd, ite_true]
    refine ⟨⟨by rw [hfail], Finset.toList_toFinset raw, rfl, rfl, by rw [hl, hlogs], rfl⟩, by simp, ?_⟩
    intro msg h; cases h

/-- A gas or recorded-proof failure is observed as a resource failure that rolls back. -/
theorem observe_gasFailure (ctx : Context) (raw : RawStorage) (codeOf : List UInt8 → Near.ContractCode)
    (o : VMOutcome) (logs : List String) (h : GasFailureUpTo o logs) :
    let r := observeW ctx raw codeOf o
    ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: logs ∧
      ∀ msg, r.outcome ≠ .error (.executionIssue msg) := by
  obtain ⟨e, hge, ha, -, -, hl⟩ := h
  have hout : ResourceFailure (observeW ctx raw codeOf o) := by
    unfold ResourceFailure
    rcases hge with rfl | rfl | ⟨n, rfl⟩
    · left; simp only [observeW, Near.Boundary.observe, ha]; rfl
    · left; simp only [observeW, Near.Boundary.observe, ha]; rfl
    · right; simp only [observeW, Near.Boundary.observe, ha]; rfl
  have hrb : ∀ {f : Failure}, (observeW ctx raw codeOf o).outcome = .error f →
      RolledBack ctx raw (observeW ctx raw codeOf o) := fun hf => by
    have := Near.Boundary.observe_rolledBack ctx raw.toList o _ _ hf
    rw [Finset.toList_toFinset] at this
    exact this
  refine ⟨hout, hout.elim hrb hrb, ?_, ?_⟩
  · simp only [observeW, Near.Boundary.observe, ha]
    exact hl
  · intro msg h'
    rcases hout with h | h <;> rw [h] at h' <;> cases h'

/-- A step agreeing with a host agrees with any host equal to it up to gas
and the recorded proof. -/
theorem AgreesWith.congr {M : ContractModel} {ctx : Context} {raw : RawStorage} {e e' : NearState}
    {res : StepResult M.Panic M.State M.Ret M.Promise} (h : AgreesWith M ctx raw e res)
    (he : eraseP e = eraseP e') : AgreesWith M ctx raw e' res := by
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (eraseP x) = f x) → f e = f e' :=
    fun f hfe => eraseP_field he f hfe
  have u : e.context.storageUsage.toNat = e'.context.storageUsage.toNat :=
    hf (fun x => x.context.storageUsage.toNat) fun _ => rfl
  have b : e.context.accountBalance = e'.context.accountBalance := hf (fun x => x.context.accountBalance) fun _ => rfl
  have r : returnOf e = returnOf e' := hf returnOf fun _ => rfl
  have s : finalStorage e = finalStorage e' := hf finalStorage fun _ => rfl
  have l : logsOf e = logsOf e' := hf logsOf fun _ => rfl
  cases res with
  | ok o =>
    simp only [AgreesWith] at h ⊢
    rw [← u, ← b, ← r, ← s, ← l]
    exact h
  | error f =>
    simp only [AgreesWith] at h ⊢
    rw [← u, ← b, ← l]
    exact h

/-- **The boundary.** For a call of method `i` whose run `F` describes and a
model step `res` agreeing with `F`: no execution issue; with the host's
precondition (which may need room in the recorded proof), room for loading
and the method within `Cg` and `Cg` attached, the model's step using at most
`Cg`; under any gas and any recorded proof, the model's step or a resource
failure that rolls back with a prefix of the model's logs. The latter needs
the precondition only of the host recording no proof (`hpreP`), and `F` to
ignore the recorded proof (`hFP`). -/
theorem method_boundary (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) {i : Nat} (Pre : NearState → Prop) (cost : NearState → Nat)
    (F : NearState → NearState) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRuns ctx.protocol i Pre cost F) (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hnp : NoPromises (F (erase (hostOf ctx raw))))
    (hFP : eraseP (F (eraseP (hostOf ctx raw))) = eraseP (F (erase (hostOf ctx raw))))
    (res : StepResult M.Panic M.State M.Ret M.Promise)
    (hag : AgreesWith M ctx raw (F (erase (hostOf ctx raw))) res) (Cg : Nat) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (Pre (erase (hostOf ctx raw)) →
      chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ Cg →
      Cg ≤ ctx.gasLimit → Matches M ctx raw r res ∧ r.usedGas ≤ Cg) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hpos : 0 < minOpCost ctx.protocol.wasm := Nat.lt_min.mpr hwf.opCost_pos
  simp only [execOn_wCode]
  have hnpP : NoPromises (F (eraseP (hostOf ctx raw))) :=
    ⟨(eraseP_field hFP NearState.promises fun _ => rfl).trans hnp.promises,
      (eraseP_field hFP NearState.returnedPromise fun _ => rfl).trans hnp.returned,
      (eraseP_field hFP NearState.gasWeights fun _ => rfl).trans hnp.weights⟩
  have hagP := hag.congr hFP.symm
  have hany := method_vm_any ctx.protocol size ctx.method (Near.Boundary.toVMContext ctx) raw.toList Pre cost F
    hpos hp.limit hp.pagesMin hp.pagesMax hname hexp hft h1 h2 hspec hpreP hnpP
  simp only at hany
  have hlogs := hagP.logs
  refine ⟨?_, ?_, ?_⟩
  · rcases hany with hg | he
    · exact (observe_gasFailure ctx raw codeOf _ _ hg).2.2.2
    · exact (observe_effects M ctx raw codeOf _ _ he res hagP).2.2
  · intro hpre hgas hlim
    have hused0 : (hostOf ctx raw).gas.used = 0 := rfl
    have hmb : (hostOf ctx raw).gas.maxBurnt = ctx.protocol.wasm.limits.maxGasBurnt := rfl
    have hpp : (hostOf ctx raw).gas.prepaid = ctx.prepaidGas := rfl
    obtain ⟨heff, hu, hbu⟩ := method_vmOutcome ctx.protocol size ctx.method (Near.Boundary.toVMContext ctx)
      raw.toList Pre cost F Cg hpos hp.limit hp.pagesMin hp.pagesMax hname hexp hft h1 h2 hspec hpre hnp
      (by show 0 + chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ Cg; omega)
      (by show Cg ≤ (hostOf ctx raw).gas.maxBurnt; rw [hmb]; exact Nat.le_trans hlim (Nat.min_le_right _ _))
      (by show Cg ≤ (hostOf ctx raw).gas.prepaid; rw [hpp]; exact Nat.le_trans hlim (Nat.min_le_left _ _))
    obtain ⟨hm, hug, -⟩ := observe_effects M ctx raw codeOf _ _ heff res hag
    refine ⟨hm, ?_⟩
    rcases hug with h | h
    · rw [h]; exact hu
    · rw [h]; exact Nat.le_trans hbu hu
  · rcases hany with hg | he
    · right
      obtain ⟨ho, hrb, hl, -⟩ := observe_gasFailure ctx raw codeOf _ _ hg
      exact ⟨ho, hrb, by rw [hlogs]; exact hl⟩
    · left
      exact (observe_effects M ctx raw codeOf _ _ he res hagP).1

/-- **The clauses of `Refines` for a call to the method.** For a call `c`
whose model step agrees with `F`, whose gas bound covers loading and the
method's cost, and whose precondition on the host holds when the recorded
proof has room for the model's bound. -/
theorem method_refines_call (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option M.State) (ctx : Context) (c : M.Call) {i : Nat}
    (Pre : NearState → Prop) (cost : NearState → Nat) (F : NearState → NearState)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hname : ctx.method.isEmpty = false) (hexp : wNearModule.exportFunc? ctx.method = some i)
    (hft : wNearModule.funcType? i = some { params := [], results := [] }) (h1 : 48 ≤ i) (h2 : i < 955)
    (hspec : MethodRuns ctx.protocol i Pre cost F)
    (hpre : ctx.ProofRoom (M.proofBound ctx st c) → Pre (erase (hostOf ctx raw)))
    (hpreP : Pre (eraseP (hostOf ctx raw)))
    (hnp : NoPromises (F (erase (hostOf ctx raw))))
    (hFP : eraseP (F (eraseP (hostOf ctx raw))) = eraseP (F (erase (hostOf ctx raw))))
    (hag : AgreesWith M ctx raw (F (erase (hostOf ctx raw))) (M.step ctx st c))
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) + cost (erase (hostOf ctx raw)) ≤ M.gas ctx st c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := M.step ctx st c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (M.gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom (M.proofBound ctx st c) →
      Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hni, hen, hany⟩ := method_boundary M size codeOf raw ctx Pre cost F hp hwf hname hexp hft h1 h2
    hspec hpreP hnp hFP (M.step ctx st c) hag (M.gas ctx st c)
  exact ⟨hni, fun hgas hroom => hen (hpre hroom) hbound hgas, hany⟩

end WNear.Binary
