import Bridge.Methods.StorageMinimumBalanceUninit
import Bridge.Methods.FtTotalSupplyAll
import Bridge.Functions.ToVecTwo

/-!
# `storage_minimum_balance` (231) refines the model

The model's side of `storageMinimumBalance_refines`, as for `ft_total_supply`
(`FtTotalSupplyModel`, `FtTotalSupplyGas`, `FtTotalSupplyPre`):

* `usage_of_header`, `minJson_eq_jsonU128`: the binary returns the JSON of
  `(accountStorageUsage mod 2^64) · 10^19`; on a well-formed state (`usage_lt`) that is the
  model's `storageMin`. No state the model represents makes them differ.
* `hag_wnear`: the model's step agrees with every final host.
* `cost_le`, `hbound_wnear`: the model's gas bound covers loading and the method's cost, under
  `CostsV86` (no new premise: 231 costs 309 `regular_op_cost`s more than 296, within the same
  bound).
* `readOk_of`, `pre_of_ctx`: the host reads the model state, from the context (`LimitsV86`).
* `storageMinimumBalance_refines_init`, and `storageMinimumBalance_refines_all` on any storage
  the model represents.
-/

namespace WNear.Binary.StorageMinimumBalanceMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface ContractModel WNear.Binary
open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.StorageMinimumBalance
  WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.StorageBalanceBounds (u128Of)

/-! ## The model's step and the returned JSON -/

/-- The model's step for `storage_minimum_balance` on the state `S`. -/
theorem step_eq (cfg : WNear.Config) (ctx : Context) (S : WNear.State) :
    (WNear.wnear cfg).step ctx (some S) .storageMinimumBalance =
      if 0 < deficit ctx S then .error { failure := .lackBalanceForState (deficit ctx S), logs := [] }
      else .ok { state := S, ret := .u128 S.storageMin, logs := [], promises := [] } := by
  rfl

/-- The storage usage in the header of `S` is the one in an equal header of a well-formed `S'`. -/
theorem usage_of_header {S S' : WNear.State} (hS' : S'.WF) (h : WNear.header S = WNear.header S') :
    S.accountStorageUsage % 2 ^ 64 = S'.accountStorageUsage := by
  simp only [WNear.header] at h
  have hlen : (Borsh.bytes WNear.accountsPrefix ++ Borsh.u128 S.totalSupply).length =
      (Borsh.bytes WNear.accountsPrefix ++ Borsh.u128 S'.totalSupply).length := by
    simp only [List.length_append, Borsh.u128, Borsh.leBytes_length]
  have hs := congrArg Memory.decodeLE (List.append_inj_right h hlen)
  simp only [Borsh.u64, decodeLE_leBytes] at hs
  have hlt := hS'.usage_lt
  simp only [WNear.u64Bound] at hlt
  rw [show (256 : Nat) ^ 8 = 2 ^ 64 by norm_num] at hs
  rw [hs, Nat.mod_eq_of_lt hlt]

/-- The binary's return bytes are the model's. -/
theorem minJson_eq_jsonU128 {S S' : WNear.State} (hS' : S'.WF) (h : WNear.header S = WNear.header S') :
    minJson S = (WNear.jsonU128 S'.storageMin).toUTF8.toList := by
  rw [jsonU128_bytes, minJson, minS, usage_of_header hS' h]
  rfl

theorem minJson_length (S : WNear.State) : (minJson S).length ≤ 41 := by
  have : minS S < 10 ^ 39 := by have := minS_lt S; norm_num at this ⊢; omega
  have := FmtDigits.decDigits_length_le 39 _ (by norm_num) this
  simp only [minJson, jsonOf, List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## The final host -/

theorem post_field {α : Type} (f : NearState → α) (hf : ∀ x, f (erase x) = f x)
    (hsel : ∀ x b, f (x.selectReturnValue b) = f x) (hreg : ∀ x i v, f (x.setRegister i v) = f x)
    (hacc : ∀ x a, f { x with storageAccounting := a } = f x)
    {S : WNear.State} {h0 e : NearState} (hp : post S h0 e) : f e = f h0 := by
  obtain ⟨st, h1, -, ⟨s2, -, -, he⟩, rfl⟩ := hp
  rw [hf, hsel, erase_field he f hf]
  unfold storageReadRegs
  split
  · split
    · exact hacc _ _
    · rw [hreg]; exact hacc _ _
  · exact hacc _ _

theorem post_returnData {S : WNear.State} {h0 e : NearState} (hp : post S h0 e) :
    e.returnData = some (minJson S) := by
  obtain ⟨st, h1, -, -, rfl⟩ := hp
  rfl

open WNear in
/-- **`hag` for `storage_minimum_balance`**: as `FtTotalSupplyMethod.hag_wnear`, the return
data the JSON of `storageMin`. -/
theorem hag_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (h0 : NearState) (hh0 : eraseP h0 = eraseP (hostOf ctx raw)) :
    ∀ e, post S h0 e →
      AgreesWith (wnear cfg) ctx raw e ((wnear cfg).step ctx st .storageMinimumBalance) := by
  intro e hp
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (eraseP x) = f x) → f h0 = f (hostOf ctx raw) :=
    fun f hfe => eraseP_field hh0 f hfe
  cases st with
  | none =>
    have h0 : raw = ∅ := hrep
    rw [hostOf_storage, h0] at hval
    simp at hval
  | some S' =>
    obtain ⟨hinv, hraw⟩ := (show Inv cfg S' ∧ raw = encode S' from hrep)
    have hmem := hostOf_storage_mem hval
    rw [hraw] at hmem
    have hhd : WNear.header S = WNear.header S' := mem_encode_state hmem
    have hbal : e.context.accountBalance = ctx.balance + ctx.attached :=
      (post_field (fun x => x.context.accountBalance) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.accountBalance) fun _ => rfl)
    have hsu : e.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
      (post_field (fun x => x.context.storageUsage) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.storageUsage) fun _ => rfl)
    have hsto : e.storage = (hostOf ctx raw).storage :=
      (post_field NearState.storage (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storage fun _ => rfl)
    have hkeys : e.storageKeys = (hostOf ctx raw).storageKeys :=
      (post_field NearState.storageKeys (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storageKeys fun _ => rfl)
    have hlogs : e.logs = [] :=
      (post_field NearState.logs (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.logs fun _ => rfl)
    have hfin : finalStorage e = finalStorage (hostOf ctx raw) := by
      simp only [finalStorage, hsto, hkeys]
    have hroom := hwf.usage_room
    have hge := hwf.usage_ge
    have hsuN : e.context.storageUsage.toNat = ctx.storageUsage := by
      rw [hsu, UInt64.toNat_ofNat_of_lt' (by show _ < 2 ^ 64; omega)]
    have hafter : WNear.usageAfter ctx (some S') S' = ctx.storageUsage := by
      simp only [WNear.usageAfter, WNear.storageOf]
      rw [← hraw]
      omega
    have hdef : deficit ctx S' =
        stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked := by
      rw [deficit, hafter, hsuN, hbal]
    erw [step_eq]
    split
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact hpos, by rw [← hdef]; rfl, ?_⟩
      show [] = logsOf e
      simp [logsOf, hlogs]
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact Nat.eq_zero_of_not_pos hpos, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
      · show returnOf e = .value (WNear.jsonU128 S'.storageMin).toUTF8.toList
        rw [returnOf, post_returnData hp, minJson_eq_jsonU128 hinv.toWF hhd]
      · show (finalStorage e).toFinset = encode S'
        rw [hfin, finalStorage_hostOf ctx raw hwf.raw_keys_unique, hraw]
      · exact hbal
      · show e.context.storageUsage.toNat = _ - _ + storageUsageOf ctx.protocol (encode S')
        rw [hsuN, ← hraw]
        omega
      · show logsOf e = []
        simp [logsOf, hlogs]

/-! ## The gas bound -/

/-- The arithmetic of `cost_le`, for any `u128` words `lo`, `hi` and returned bytes `j`. -/
theorem cost_le_gen (rc : RuntimeConfig) (h : NearState) (S : WNear.State) (x96 : Nat) (lo hi : UInt64)
    (j : List UInt8) (hv : h.storage WNear.stateKey = some (WNear.header S)) :
    9 * rc.wasm.regularOpCost + (2658 * rc.wasm.regularOpCost + cost219 rc.wasm h S +
      (ToVec.cost96 rc.wasm lo hi + x96) + valueReturnUse h j.length) ≤
      22000 * rc.wasm.regularOpCost + 4 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h j.length +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h j.length + x96 := by
  have a := c96 rc.wasm lo hi
  have b := c161 rc.wasm
  have d := c687 rc.wasm
  have e := readNodes_mul_le h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey)
  rw [← StateRead.stateKey_eq] at hv
  simp only [cost219, storageReadUse, StorageReadWrap.costS, ReadRegister.costRest,
    registerLenUse, readRegisterUse, valueReturnUse, hv, StateReadModel.header_length, storageReadPhaseUse,
    Option.map_some, Option.getD_some, chargesUse, storageReadBeforeCharges, storageReadValueCharges,
    writeReg, registerLenChargeList, readRegisterChargeList, valueReturnChargeList, List.map, List.sum_cons,
    List.sum_nil, chargeUse, extUse, List.cons_append, List.nil_append,
    show ¬ (29 > 4000) by decide, ite_false]
  omega

theorem cost_le (rc : RuntimeConfig) (h : NearState) (S : WNear.State) (x96 : Nat)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) :
    cost rc S x96 h ≤ 22000 * rc.wasm.regularOpCost + 4 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h (minJson S).length +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h (minJson S).length + x96 := by
  rw [cost, cost231_eq]
  exact cost_le_gen rc h S x96 _ _ _ hv

/-- The model's gas bound covers loading and the method's cost (`x96 ≤ 3·10^12`). -/
theorem hbound_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (x96 size : Nat)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) (hx : x96 ≤ 3 * 10 ^ 12) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + cost ctx.protocol S x96 (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .storageMinimumBalance := by
  have hcost := cost_le ctx.protocol (erase (hostOf ctx raw)) S x96 hval
  have htrie := trie_le ctx raw
  have hn := minJson_length S
  have hdata := dataGas_le ctx raw _ hn
  have hgas : (WNear.wnear cfg).gas ctx st .storageMinimumBalance =
      WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 41 := by
    show WNear.gasBound ctx .storageMinimumBalance = _
    simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
      WNear.Call.resultBytes, WNear.Call.returnBytes, retBytes]
    simp
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  have hrm := Nat.mul_le_mul hc.readMemoryByte hn
  simp only [extUse, hx'] at hcost
  rw [hgas, hl]
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.linearBase; have := hc.linearUnit; have := hc.base
  have := hc.loadingBase; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  omega

/-! ## The host reads the model state -/

/-- A host equal to the initial one up to gas and the recorded proof, with room for the
`STATE` lookup, reads the model state `S` that `STATE` holds (`ReadOkV` for `minJson S`). -/
theorem readOk_of (ctx : Context) (raw : RawStorage) (S : WNear.State) (hwf : ctx.WF raw)
    (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie
      (Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey) + 29)) :
    ReadOkV h S ctx.trie (minJson S) := by
  have hr := FtTotalSupplyMethod.readOk_of ctx raw S hwf hl hval h he hproof
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  refine ⟨hr.value, hr.acc, hr.keyLen, hr.trie, hr.zero, hr.link, hr.proof, hr.regLen, ?_⟩
  have e : (hostOf ctx raw).config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData := rfl
  rw [hcfg, e]
  have := hl.returned
  have := minJson_length S
  simpa [withinLimit] using (show (minJson S).length ≤ ctx.protocol.wasm.limits.maxLengthReturnedData by omega)

/-- **`hpre` and `hpreP` of `storage_minimum_balance`**, from the context. -/
theorem pre_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) :
    (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .storageMinimumBalance) →
        pre S (erase (hostOf ctx raw))) ∧
      pre S (eraseP (hostOf ctx raw)) := by
  refine ⟨fun hroom => ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩,
    ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩⟩
  · exact (budget_of_room hwf hroom _ rfl rfl).mono (read_le_proofBound ctx)
  · intro size hsz
    cases hsz

/-! ## Refinement -/

/-- **`storage_minimum_balance` refines the model on an initialized contract.** Left: the code
size, `CostsV86` and `LimitsV86`. -/
theorem storageMinimumBalance_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (hm : ctx.method = "storage_minimum_balance") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) .storageMinimumBalance
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) .storageMinimumBalance ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) .storageMinimumBalance) →
      Matches (WNear.wnear cfg) ctx raw r res ∧
        r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) .storageMinimumBalance) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨-, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  obtain ⟨hpre, hpreP⟩ := pre_of_ctx cfg ctx raw (some S) S hwf hl hval
  exact storageMinimumBalance_refines (WNear.wnear cfg) size codeOf raw (some S) ctx .storageMinimumBalance S 0
    (ToVecTwo.toVecAfterFree_zero ctx.protocol.wasm execLimits) hp hwf hm hpre hpreP
    (hag_wnear cfg ctx raw (some S) S hrep hwf hval _ rfl) (hag_wnear cfg ctx raw (some S) S hrep hwf hval _ rfl)
    (hbound_wnear cfg ctx raw (some S) S 0 size hval hc hsize (Nat.zero_le _))

/-- **`storage_minimum_balance` refines the model**: the clauses of `Refines` for a call to it,
on any storage the model represents: an initialized contract or none (the `PanicOnDefault`
panic). Left: the code size, `CostsV86` and `LimitsV86`. -/
theorem storageMinimumBalance_refines_all (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (st : Option WNear.State) (ctx : Context)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "storage_minimum_balance") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .storageMinimumBalance
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .storageMinimumBalance ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .storageMinimumBalance) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .storageMinimumBalance) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  cases st with
  | none => exact storageMinimumBalance_refines_uninit cfg size codeOf raw ctx hp hwf hrep hm hc hl hsize
  | some S => exact storageMinimumBalance_refines_init cfg size codeOf raw ctx S hp hwf hrep hm hc hl hsize

end WNear.Binary.StorageMinimumBalanceMethod
