import Bridge.Methods.NewPanics
import Bridge.Methods.FtTotalSupplyUninitRefines

/-!
# `new` (290) refines the model on its two panics

* `new_refines_deposit`: with a deposit (`ctx.attached ≠ 0`), whatever the state, the binary
  panics with "Method new doesn't accept deposit" (`new_panics_deposit`), as the model's step
  does (`step_new_deposit`).
* `new_refines_init`: with no deposit and a state `some S`, the binary panics with "The contract
  has already been initialized" (`new_panics_init`), as the model's step does
  (`step_new_some`).

`method_refines_callP` gives the clauses of `Refines`. The host's premises come from the
context (`preDep_of`, `initOk_of`); the gas bound (`hbound_dep`, `hbound_init`) from
`CostsV86` and `CostsNewV86` (protocol 86's `storage_has_key` costs).
-/

namespace WNear.Binary.NewMethod

open Wasm Wasm.Near NearLogic NearInterface ContractModel WNear.Binary
open WNear.Binary.FtTotalSupplyMethod (LimitsV86 budget_of_room lookup_le_proofBound hostOf_storage_of_mem
  postNone_panicHost CostsV86 trie_le)
open WNear.Binary.EnvGetters (depLo depHi depLo_or_depHi_eq_zero)
open WNear.Binary.NewBody (costDep290 costInit290 storageHasKeyPost_fields)

/-- The protocol-86 values (`runtime_config_v86.json`, `wasm_config`) of the cost parameters of
`storage_has_key`, as upper bounds (what `new`'s panic paths pay beyond `CostsV86`). -/
structure CostsNewV86 (p : RuntimeConfig) : Prop where
  storageHasKeyBase : p.wasm.extCosts.cost "storage_has_key_base" ≤ 54039896625
  storageHasKeyByte : p.wasm.extCosts.cost "storage_has_key_byte" ≤ 30790845

/-! ## The host's premises, from the context -/

/-- A host equal to the initial one up to gas and the recorded proof meets `PreDep` when the
call attaches a deposit. -/
theorem preDep_of (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hc : CostsV86 ctx.protocol) (hd : ctx.attached ≠ 0) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) : PreDep h := by
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hlogs : h.logs = (hostOf ctx raw).logs := eraseP_field he NearState.logs fun _ => rfl
  have hext : h.extCosts = (hostOf ctx raw).extCosts := eraseP_field he NearState.extCosts fun _ => rfl
  have hatt : h.context.attachedDeposit = ctx.attached :=
    eraseP_field he (fun x => x.context.attachedDeposit) fun _ => rfl
  refine ⟨eraseP_field he (fun x => x.context.isView) fun _ => rfl, ?_, ?_, ?_⟩
  · intro h0
    have hlt : ctx.attached < 2 ^ 128 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hwf.balance_lt
    rw [depLo_or_depHi_eq_zero, hatt, Nat.mod_eq_of_lt hlt] at h0
    exact hd h0
  · intro limit hm
    rw [hcfg] at hm
    have e : (hostOf ctx raw).config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := rfl
    rw [e, Option.some.injEq] at hm
    subst hm
    rw [hlogs]
    have := hl.totalLog
    show 0 + 33 ≤ _
    omega
  · rw [hext]
    have := hc.readMemoryByte
    show ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 33 < 2 ^ 64
    omega

/-- A host equal to the initial one up to gas and the recorded proof, with no deposit, `STATE`
present and room for its lookup, meets `InitOk` with the context's trie. -/
theorem initOk_of (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hc : CostsV86 ctx.protocol) (hd : ctx.attached = 0) (v : List UInt8)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some v) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie
      (Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey))) :
    InitOk h ctx.trie := by
  have hsto : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  have hacc : h.storageAccounting = some ctx.trie :=
    eraseP_field he NearState.storageAccounting fun _ => rfl
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hlogs : h.logs = (hostOf ctx raw).logs := eraseP_field he NearState.logs fun _ => rfl
  have hext : h.extCosts = (hostOf ctx raw).extCosts := eraseP_field he NearState.extCosts fun _ => rfl
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x => x.context.currentAccountId) fun _ => rfl
  have hatt : h.context.attachedDeposit = ctx.attached :=
    eraseP_field he (fun x => x.context.attachedDeposit) fun _ => rfl
  have hk := StateRead.stateKey_eq
  refine ⟨eraseP_field he (fun x => x.context.isView) fun _ => rfl, ?_, ⟨v, by rw [hsto, hk]; exact hval⟩, hacc, ?_, hwf.trie_canonical,
    hwf.trie_no_zero_hash, ?_, ?_, ?_, ?_⟩
  · rw [depLo_or_depHi_eq_zero, hatt, hd, Nat.zero_mod]
  · have e : (hostOf ctx raw).config.maxStorageKeyLen = some ctx.protocol.wasm.limits.maxLengthStorageKey := rfl
    rw [hcfg, e]
    have := hl.storageKey
    simpa [withinLimit] using (show 5 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey by omega)
  · rw [hsto, hid, hk]
    exact hostOf_storage_view ctx raw hwf WNear.stateKey
  · rw [hid, hk]; exact hproof
  · intro limit hm
    rw [hcfg] at hm
    have e : (hostOf ctx raw).config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := rfl
    rw [e, Option.some.injEq] at hm
    subst hm
    rw [hlogs]
    have := hl.totalLog
    show 0 + 41 ≤ _
    omega
  · rw [hext]
    have := hc.readMemoryByte
    show ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 41 < 2 ^ 64
    omega

/-! ## The model's side -/

theorem gas_new (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) :
    (WNear.wnear cfg).gas ctx st .new = WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 0 := by
  show WNear.gasBound ctx .new = _
  simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
    WNear.Call.resultBytes, WNear.Call.returnBytes]
  simp

theorem agreesPanic_dep (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) (hd : ctx.attached ≠ 0)
    (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) depositStr e ((WNear.wnear cfg).step ctx st .new) :=
  ⟨_, step_new_deposit cfg ctx st hd, rfl, hl.symm⟩

theorem agreesPanic_init (cfg : WNear.Config) (ctx : Context) (S : WNear.State) (hd : ctx.attached = 0)
    (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) initStr e ((WNear.wnear cfg).step ctx (some S) .new) :=
  ⟨_, step_new_some cfg ctx S hd, rfl, hl.symm⟩

theorem postDep_panicHost {e0 e : NearState} (h0 : e0.lastExecutionIssue = none) (hp : postDep e0 e) :
    PanicHost depositStr e := by
  subst hp
  exact ⟨rfl, h0⟩

theorem postDep_logs {e0 e : NearState} (h0 : e0.logs = []) (hp : postDep e0 e) : logsOf e = [] := by
  subst hp
  show (e0.logs.map _) = []
  rw [h0]
  rfl

theorem postInit_panicHost {e0 e : NearState} (h0 : e0.lastExecutionIssue = none) (hp : postInit e0 e) :
    PanicHost initStr e := by
  obtain ⟨st, h2, -, hq, rfl⟩ := hp
  obtain ⟨-, -, -, hi⟩ := storageHasKeyPost_fields hq
  exact ⟨rfl, hi.trans h0⟩

theorem postInit_logs {e0 e : NearState} (h0 : e0.logs = []) (hp : postInit e0 e) : logsOf e = [] := by
  obtain ⟨st, h2, -, hq, rfl⟩ := hp
  obtain ⟨-, hl, -, -⟩ := storageHasKeyPost_fields hq
  show (h2.logs.map _) = []
  rw [hl, h0]
  rfl

/-! ## The gas bounds -/

theorem loading_eq (ctx : Context) (raw : RawStorage) (size : Nat) :
    chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
  simp [chargesUse, loadingCharges, chargeUse]; rfl

/-- **The model's gas bound covers loading and the deposit panic.** -/
theorem hbound_dep (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (size : Nat) (hc : CostsV86 ctx.protocol) (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + costDep ctx.protocol (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .new := by
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  rw [gas_new, loading_eq]
  simp only [costDep, costDep290, attachedDepositUse, attachedDepositChargeList, panicUtf8Use, panicUtf8Charges,
    chargesUse, chargeUse, List.map, List.sum_cons, List.sum_nil, hx']
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.base; have := hc.loadingBase; have := hc.readMemoryBase
  have := hc.readMemoryByte; have := hc.writeMemoryBase; have := hc.writeMemoryByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  omega

/-- **The model's gas bound covers loading and the "already initialized" panic.** -/
theorem hbound_init (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (size : Nat) (hc : CostsV86 ctx.protocol) (hcn : CostsNewV86 ctx.protocol) (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + costInit ctx.protocol (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .new := by
  have htrie := trie_le ctx raw
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  rw [gas_new, loading_eq]
  simp only [costInit, costInit290, attachedDepositUse, attachedDepositChargeList, panicUtf8Use, panicUtf8Charges,
    storageHasKeyUse, storageHasKeyBeforeCharges, chargesUse, chargeUse, List.map, List.sum_cons, List.sum_nil,
    hx'] at htrie ⊢
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.base; have := hc.loadingBase; have := hc.readMemoryBase
  have := hc.readMemoryByte; have := hc.writeMemoryBase; have := hc.writeMemoryByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  have := hcn.storageHasKeyBase; have := hcn.storageHasKeyByte
  omega

/-! ## The clauses of `Refines` -/

/-- **`new` refines the model on a deposit**: whatever the state, the binary panics with
"Method new doesn't accept deposit", as the model's step does. -/
theorem new_refines_deposit (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (st : Option WNear.State) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st) (hm : ctx.method = "new")
    (hd : ctx.attached ≠ 0) (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .new
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .new ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .new) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .new) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have _ := hrep
  exact method_refines_callP (WNear.wnear cfg) size codeOf raw st ctx .new PreDep
    (costDep ctx.protocol) postDep depositStr hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_290)
    funcType_290 (by decide) (by decide) (new_panics_deposit ctx.protocol)
    (fun _ => preDep_of ctx raw hwf hl hc hd _ rfl) (preDep_of ctx raw hwf hl hc hd _ rfl)
    (fun e he => postDep_panicHost rfl he) (fun e he => postDep_panicHost rfl he)
    (fun e he => agreesPanic_dep cfg ctx st hd e (postDep_logs rfl he))
    (fun e he => agreesPanic_dep cfg ctx st hd e (postDep_logs rfl he))
    (hbound_dep cfg ctx raw st size hc hsize)

/-- **`new` refines the model on an initialized contract with no deposit**: the binary panics
with "The contract has already been initialized", as the model's step does. -/
theorem new_refines_init (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (S : WNear.State) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw (some S)) (hm : ctx.method = "new")
    (hd : ctx.attached = 0) (hc : CostsV86 ctx.protocol) (hcn : CostsNewV86 ctx.protocol)
    (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) .new
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) .new ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) .new) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) .new) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨-, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  exact method_refines_callP (WNear.wnear cfg) size codeOf raw (some S) ctx .new preInit
    (costInit ctx.protocol) postInit initStr hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_290)
    funcType_290 (by decide) (by decide) (new_panics_init ctx.protocol)
    (fun hroom => ⟨ctx.trie, initOk_of ctx raw hwf hl hc hd _ hval _ rfl
      ((budget_of_room hwf hroom _ rfl rfl).mono (lookup_le_proofBound ctx))⟩)
    ⟨ctx.trie, initOk_of ctx raw hwf hl hc hd _ hval _ rfl (by intro size hsz; cases hsz)⟩
    (fun e he => postInit_panicHost rfl he) (fun e he => postInit_panicHost rfl he)
    (fun e he => agreesPanic_init cfg ctx S hd e (postInit_logs rfl he))
    (fun e he => agreesPanic_init cfg ctx S hd e (postInit_logs rfl he))
    (hbound_init cfg ctx raw (some S) size hc hcn hsize)

end WNear.Binary.NewMethod
