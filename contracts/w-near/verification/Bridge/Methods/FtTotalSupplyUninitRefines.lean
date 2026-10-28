import Bridge.Methods.FtTotalSupplyNoneRun
import Bridge.Methods.FtTotalSupplyPre
import Bridge.Methods.Panics

/-!
# `ft_total_supply` (296) refines the model on an uninitialized contract

`ftTotalSupply_refines_uninit`: with no state (`raw = ∅`), the binary panics with "The contract
is not initialized" (`ftTotalSupply_panics`) and the model's step is that panic
(`agreesPanic_none`); `method_refines_callP` gives the clauses of `Refines`.

* `preNone_of_ctx`: the initial host meets `ReadNone`: no `STATE` (`raw = ∅`), the storage
  premises from `Context.WF` (as `pre_of_ctx`), the 31-byte message within the total log limit
  (no logs yet; `LimitsV86.totalLog`) and its `read_memory_byte` cost a `u64` (`CostsV86`).
* `postNone_panicHost`, `postNone_logs`: every final host panicked with that message, with no
  execution issue and no logs.
* `hbound_none`: loading plus the path's cost is within the model's gas bound
  (`CostsV86`, with `utf8_decoding_base` and `utf8_decoding_byte`, the costs of `panic_utf8`).
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near NearLogic NearInterface WNear.Binary FtTotalSupply

/-- The initial host on no state reads nothing. -/
theorem hostOf_storage_empty (ctx : Context) (k : List UInt8) : (hostOf ctx ∅).storage k = none := by
  rw [hostOf_storage, Finset.toList_empty]
  rfl

/-- A host equal to the initial one up to gas and the recorded proof, with no `STATE` and room
for the `STATE` lookup, meets `ReadNone`. -/
theorem readNone_of (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hc : CostsV86 ctx.protocol) (hval : (hostOf ctx raw).storage WNear.stateKey = none) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie
      (Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey))) :
    ReadNone h ctx.trie := by
  have hsto : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  have hacc : h.storageAccounting = some ctx.trie :=
    eraseP_field he NearState.storageAccounting fun _ => rfl
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x => x.context.currentAccountId) fun _ => rfl
  have hlogs : h.logs = (hostOf ctx raw).logs := eraseP_field he NearState.logs fun _ => rfl
  have hext : h.extCosts = (hostOf ctx raw).extCosts := eraseP_field he NearState.extCosts fun _ => rfl
  refine ⟨?_, hacc, ?_, hwf.trie_canonical, hwf.trie_no_zero_hash, ?_, ?_, ?_, ?_⟩
  · rw [hsto]; exact hval
  · have e : (hostOf ctx raw).config.maxStorageKeyLen = some ctx.protocol.wasm.limits.maxLengthStorageKey := rfl
    rw [hcfg, e]
    have := hl.storageKey
    simpa [withinLimit] using (show 5 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey by omega)
  · rw [hsto, hid]
    exact hostOf_storage_view ctx raw hwf WNear.stateKey
  · rw [hid]; exact hproof
  · intro limit hm
    rw [hcfg] at hm
    have e : (hostOf ctx raw).config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength := rfl
    rw [e, Option.some.injEq] at hm
    subst hm
    rw [hlogs]
    have := hl.totalLog
    show 0 + 31 ≤ _
    omega
  · rw [hext]
    have := hc.readMemoryByte
    show ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 31 < 2 ^ 64
    omega

/-- **`hpre` and `hpreP` on an uninitialized contract**, from the context: the initial host
meets `ReadNone` given room for the model's proof bound, and the host recording no proof
always. -/
theorem preNone_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol) (hc : CostsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = none) :
    (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) → preNone (erase (hostOf ctx raw))) ∧
      preNone (eraseP (hostOf ctx raw)) := by
  refine ⟨fun hroom => ⟨ctx.trie, readNone_of ctx raw hwf hl hc hval _ rfl ?_⟩,
    ⟨ctx.trie, readNone_of ctx raw hwf hl hc hval _ rfl ?_⟩⟩
  · exact (budget_of_room hwf hroom _ rfl rfl).mono (lookup_le_proofBound ctx)
  · intro size hsz
    cases hsz

/-- Every host `postNone` allows panicked with "The contract is not initialized", with no
execution issue when the initial one had none. -/
theorem postNone_panicHost {e0 e : NearState} (h0 : e0.lastExecutionIssue = none) (hp : postNone e0 e) :
    PanicHost notInitMsg e := by
  obtain ⟨st, h1, -, hq, rfl⟩ := hp
  obtain ⟨-, -, -, hi⟩ := storageReadPost_fields hq
  exact ⟨rfl, hi.trans h0⟩

/-- Every host `postNone` allows has no logs when the initial one had none. -/
theorem postNone_logs {e0 e : NearState} (h0 : e0.logs = []) (hp : postNone e0 e) : logsOf e = [] := by
  obtain ⟨st, h1, -, hq, rfl⟩ := hp
  obtain ⟨-, hl, -, -⟩ := storageReadPost_fields hq
  show (h1.logs.map _) = []
  rw [hl, h0]
  rfl

open NearInterface FtTotalSupply in
/-- **The model's gas bound covers loading and the panic path.** -/
theorem hbound_none (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (size : Nat) (hval : (hostOf ctx raw).storage WNear.stateKey = none) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + costNone ctx.protocol (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .ftTotalSupply := by
  have htrie := trie_le ctx raw
  have hgas : (WNear.wnear cfg).gas ctx st .ftTotalSupply =
      WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 41 := by
    show WNear.gasBound ctx .ftTotalSupply = _
    simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
      WNear.Call.resultBytes, WNear.Call.returnBytes, retBytes]
    simp
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hv : (erase (hostOf ctx raw)).storage StateRead.stateKey = none := by
    rw [StateRead.stateKey_eq]; exact hval
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  rw [hgas, hl]
  simp only [costNone, cost296None, storageReadUse, storageReadPhaseUse, hv, Option.map_none,
    Option.getD_none, panicUtf8Use, panicUtf8Charges, storageReadBeforeCharges, chargesUse, chargeUse,
    List.map, List.sum_cons, List.sum_nil, hx'] at htrie ⊢
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.base; have := hc.loadingBase; have := hc.readMemoryBase
  have := hc.readMemoryByte; have := hc.storageReadBase; have := hc.storageReadKeyByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  omega

open ContractModel in
/-- **`ft_total_supply` refines the model on an uninitialized contract**: with no state, the
binary panics with "The contract is not initialized", as the model's step does. Left: the code
size, `CostsV86` and `LimitsV86`. -/
theorem ftTotalSupply_refines_uninit (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hrep : (WNear.wnear cfg).Represents raw none) (hm : ctx.method = "ft_total_supply")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none .ftTotalSupply
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none .ftTotalSupply ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none .ftTotalSupply) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none .ftTotalSupply) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  subst hraw
  have hval : (hostOf ctx ∅).storage WNear.stateKey = none := hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := preNone_of_ctx cfg ctx ∅ none hwf hl hc hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf ∅ none ctx .ftTotalSupply preNone
    (costNone ctx.protocol) postNone notInitMsg hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_296)
    funcType_296 (by decide) (by decide) (ftTotalSupply_panics ctx.protocol) hpre hpreP
    (fun e he => postNone_panicHost rfl he) (fun e he => postNone_panicHost rfl he)
    (fun e he => agreesPanic_none cfg ctx e (postNone_logs rfl he))
    (fun e he => agreesPanic_none cfg ctx e (postNone_logs rfl he))
    (hbound_none cfg ctx ∅ none size hval hc hsize)

end WNear.Binary.FtTotalSupplyMethod
