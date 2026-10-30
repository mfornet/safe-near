import Bridge.Methods.FtMetadata
import Bridge.Methods.StorageBalanceBoundsRefines

/-!
# `ft_metadata` (309) refines the model

The model's side of `ftMetadata_refines`, as for `storage_balance_bounds`
(`StorageBalanceBoundsRefines`):

* `hag_wnear`: the model's step agrees with every final host (the return data is the model's JSON,
  `metaJson_eq`).
* `cost_le`, `hbound_wnear`: the model's gas bound (`gas_309`: `computeGas`, the trie nodes and
  138 bytes of return data) covers loading and the method's cost under `CostsV86`. No new
  premise: the cost is at most 80000 `regular_op_cost`s, thirteen linear-op charges and the host
  calls' (every write of the `u8` field is charged the realloc's price, `WriteSink.costW`).
* `readOk_of`, `pre_of_ctx`: the host reads the model state, from the context (`LimitsV86`).
* `ftMetadata_refines_init`, and `ftMetadata_refines_all` on any storage the model represents.
-/

namespace WNear.Binary.FtMetadataMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface ContractModel WNear.Binary
open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.FtMetadataBody
  WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.MetadataFields (metaJson metaJson_length)

/-! ## The model's step -/

/-- The model's step for `ft_metadata` on the state `S`. -/
theorem step_eq (cfg : WNear.Config) (ctx : Context) (S : WNear.State) :
    (WNear.wnear cfg).step ctx (some S) .ftMetadata =
      if 0 < deficit ctx S then .error { failure := .lackBalanceForState (deficit ctx S), logs := [] }
      else .ok { state := S, ret := .metadata WNear.metadata, logs := [], promises := [] } := by
  rfl

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
    e.returnData = some metaJson := by
  obtain ⟨st, h1, -, -, rfl⟩ := hp
  rfl

open WNear in
/-- **`hag` for `ft_metadata`**: as `StorageBalanceBoundsMethod.hag_wnear`, the return data the
metadata's JSON. -/
theorem hag_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (h0 : NearState) (hh0 : eraseP h0 = eraseP (hostOf ctx raw)) :
    ∀ e, post S h0 e →
      AgreesWith (wnear cfg) ctx raw e ((wnear cfg).step ctx st .ftMetadata) := by
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
      · show returnOf e = .value (WNear.Ret.metadata WNear.metadata).json.toUTF8.toList
        rw [returnOf, post_returnData hp, metaJson_eq]
      · show (finalStorage e).toFinset = encode S'
        rw [hfin, finalStorage_hostOf ctx raw hwf.raw_keys_unique, hraw]
      · exact hbal
      · show e.context.storageUsage.toNat = _ - _ + storageUsageOf ctx.protocol (encode S')
        rw [hsuN, ← hraw]
        omega
      · show logsOf e = []
        simp [logsOf, hlogs]

/-! ## The gas bound -/

section Gas

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

/-- A write on the serializer's sink (`WriteSink.costW`) of at most 8 bytes: the realloc's price. -/
theorem cW (k : Nat) (hk : k ≤ 8) : WriteSink.costW cfg 2 128 k ≤ 4860 * c + L := by
  have hP := WriteSink.cellPages_one (UInt32.ofNat (2 * (128 : UInt32).toNat)) (by decide)
  have hm := memcpy_le k
  have hm' := Nat.mul_le_mul_right c hm
  have h18 : (18 * k + 6) * c ≤ 150 * c := Nat.mul_le_mul_right c (by omega)
  simp only [WriteSink.costW, VecGrow.costGrow, VecGrow.cost154, AllocWalk.cost581W, AllocWalk.walkCost,
    AllocWalk.wc, hP, show MemCpy.cost (UInt32.toNat 128) = 2310 by rfl]
  omega

theorem c105 : SerdeSink.cost105s cfg (WriteSink.costW cfg 2 128) (UInt32.toNat 8) ≤ 30000 * c + 6 * L := by
  have a := cW cfg 1 (by decide)
  have b := cW cfg 2 (by decide)
  have d := cW cfg (UInt32.toNat 8) (by decide)
  simp only [SerdeSink.cost105s, SerdeSink.cost344s, show UInt32.toNat 8 = 8 by rfl] at a b d ⊢
  omega

theorem c102 : MetadataStruct.cost102 cfg 2 ≤ 47000 * c + 6 * L := by
  have a := c105 cfg
  simp only [MetadataStruct.cost102, SerializeStr.cost383, SerializeStr.cost344,
    show MemCpy.cost 1 = 24 by rfl, show MemCpy.cost 4 = 78 by rfl, show MemCpy.cost (UInt32.toNat 4) = 78 by rfl,
    show MemCpy.cost (UInt32.toNat 8) = 150 by rfl, show MemCpy.cost (UInt32.toNat 27) = 492 by rfl,
    show MemCpy.cost (UInt32.toNat 6) = 114 by rfl, show MemCpy.cost (UInt32.toNat 5) = 96 by rfl,
    show MemCpy.cost (UInt32.toNat 9) = 168 by rfl, show MemCpy.cost (UInt32.toNat 14) = 258 by rfl,
    show UInt32.toNat 4 = 4 by rfl, show UInt32.toNat 8 = 8 by rfl, show UInt32.toNat 27 = 27 by rfl,
    show UInt32.toNat 6 = 6 by rfl, show UInt32.toNat 5 = 5 by rfl, show UInt32.toNat 9 = 9 by rfl,
    show UInt32.toNat 14 = 14 by rfl, show MemCpy.cost 8 = 150 by rfl, show MemCpy.cost 27 = 492 by rfl,
    show MemCpy.cost 6 = 114 by rfl, show MemCpy.cost 5 = 96 by rfl, show MemCpy.cost 9 = 168 by rfl,
    show MemCpy.cost 14 = 258 by rfl] at a ⊢
  omega

theorem c308 : MetadataGetter.cost308 cfg 2 ≤ 5000 * c + 3 * L := by
  have a := cAllocF cfg 8 (by decide)
  have b := cAllocF cfg 27 (by decide)
  have d := cAllocF cfg 5 (by decide)
  simp only [MetadataGetter.cost308, MetadataGetter.cost763, VecWithCap.costAllocF_le2 cfg (show 2 ≤ 2 by decide),
    show MemCpy.cost (UInt32.toNat 8) = 150 by rfl, show MemCpy.cost (UInt32.toNat 27) = 492 by rfl,
    show MemCpy.cost (UInt32.toNat 5) = 96 by rfl]
  omega

theorem cM309 (h : NearState) (S : WNear.State) :
    costM309 cfg h S ≤ 55000 * c + 10 * L + cost219 cfg h S := by
  have a := c102 cfg
  have b := c308 cfg
  have d := cAllocF cfg 128 pages_fixed.2.2
  simp only [costM309, VecWithCap.costAllocF_le2 cfg (show 2 ≤ 2 by decide)]
  omega

end Gas

/-- The arithmetic of `cost_le`. -/
theorem cost_le_gen (rc : RuntimeConfig) (h : NearState) (S : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) :
    10 * rc.wasm.regularOpCost + (477 * rc.wasm.regularOpCost + costM309 rc.wasm h S + 3000 * rc.wasm.regularOpCost +
      valueReturnUse h 138) ≤
      80000 * rc.wasm.regularOpCost + 13 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h 138 +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h 138 := by
  have a := cM309 rc.wasm h S
  have b := c161 rc.wasm
  have d := c687 rc.wasm
  have e := readNodes_mul_le h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey)
  rw [← StateRead.stateKey_eq] at hv
  simp only [cost219, storageReadUse, StorageReadWrap.costS, ReadRegister.costRest,
    registerLenUse, readRegisterUse, valueReturnUse, hv, StateReadModel.header_length, storageReadPhaseUse,
    Option.map_some, Option.getD_some, chargesUse, storageReadBeforeCharges, storageReadValueCharges,
    writeReg, registerLenChargeList, readRegisterChargeList, valueReturnChargeList, List.map, List.sum_cons,
    List.sum_nil, chargeUse, extUse, List.cons_append, List.nil_append,
    show ¬ (29 > 4000) by decide, ite_false] at a ⊢
  omega

theorem cost_le (rc : RuntimeConfig) (h : NearState) (S : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) :
    cost rc S h ≤ 80000 * rc.wasm.regularOpCost + 13 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h 138 +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h 138 := by
  rw [cost, cost309]
  exact cost_le_gen rc h S hv

open NearInterface in
theorem dataGas_le138 (ctx : Context) (raw : RawStorage) :
    valueReturnDataGas (erase (hostOf ctx raw)) 138 ≤ returnDataGas ctx 138 := by
  have hr : (erase (hostOf ctx raw)).outputDataReceivers = ctx.outputDataReceivers.map NearInterface.AccountId.bytes := rfl
  have hc : (erase (hostOf ctx raw)).context.currentAccountId = ctx.current.bytes := rfl
  have hf : (erase (hostOf ctx raw)).fees = ctx.protocol.fees.actionFees := rfl
  unfold valueReturnDataGas returnDataGas
  rw [hr, hc, hf, List.map_map]
  generalize ctx.outputDataReceivers = l
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp]
    have hsir : (r.bytes == ctx.current.bytes) = decide (r = ctx.current) := by
      by_cases h : r = ctx.current
      · subst h; simp
      · simp only [h, decide_false]
        exact beq_eq_false_iff_ne.2 fun e => h (bytes_inj e)
    rw [hsir]
    dsimp only at ih
    rw [Nat.add_mul]
    omega

/-- The model's gas bound covers loading and the method's cost. -/
theorem hbound_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (size : Nat)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + cost ctx.protocol S (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .ftMetadata := by
  have hcost := cost_le ctx.protocol (erase (hostOf ctx raw)) S hval
  have htrie := trie_le ctx raw
  have hdata := dataGas_le138 ctx raw
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  have hrm := Nat.mul_le_mul_right 138 hc.readMemoryByte
  simp only [extUse, hx'] at hcost
  rw [gas_309, hl]
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.linearBase; have := hc.linearUnit; have := hc.base
  have := hc.loadingBase; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  omega

/-! ## The host reads the model state -/

/-- A host equal to the initial one up to gas and the recorded proof, with room for the
`STATE` lookup, reads the model state `S` that `STATE` holds (`ReadOkV` for the 138 bytes). -/
theorem readOk_of (ctx : Context) (raw : RawStorage) (S : WNear.State) (hwf : ctx.WF raw)
    (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie
      (Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey) + 29)) :
    ReadOkV h S ctx.trie metaJson := by
  have hr := FtTotalSupplyMethod.readOk_of ctx raw S hwf hl hval h he hproof
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  refine ⟨hr.value, hr.acc, hr.keyLen, hr.trie, hr.zero, hr.link, hr.proof, hr.regLen, ?_⟩
  have e : (hostOf ctx raw).config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData := rfl
  rw [hcfg, e]
  have := hl.returned
  simpa [withinLimit, metaJson_length] using
    (show metaJson.length ≤ ctx.protocol.wasm.limits.maxLengthReturnedData by rw [metaJson_length]; omega)

/-- **`hpre` and `hpreP` of `ft_metadata`**, from the context. -/
theorem pre_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) :
    (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftMetadata) →
        pre S (erase (hostOf ctx raw))) ∧
      pre S (eraseP (hostOf ctx raw)) := by
  refine ⟨fun hroom => ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩,
    ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩⟩
  · exact (budget_of_room hwf hroom _ rfl rfl).mono (read_le_proofBound ctx)
  · intro size hsz
    cases hsz

/-! ## Refinement -/

/-- **`ft_metadata` refines the model on an initialized contract.** Left: the code size,
`CostsV86` and `LimitsV86`. -/
theorem ftMetadata_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (hm : ctx.method = "ft_metadata") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) .ftMetadata
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) .ftMetadata ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) .ftMetadata) →
      Matches (WNear.wnear cfg) ctx raw r res ∧
        r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) .ftMetadata) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨-, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  obtain ⟨hpre, hpreP⟩ := pre_of_ctx cfg ctx raw (some S) S hwf hl hval
  exact ftMetadata_refines (WNear.wnear cfg) size codeOf raw (some S) ctx .ftMetadata S
    hp hwf hm hpre hpreP
    (hag_wnear cfg ctx raw (some S) S hrep hwf hval _ rfl) (hag_wnear cfg ctx raw (some S) S hrep hwf hval _ rfl)
    (hbound_wnear cfg ctx raw (some S) S size hval hc hsize)

/-- **`ft_metadata` refines the model**: the clauses of `Refines` for a call to it, on any storage
the model represents: an initialized contract or none (the `PanicOnDefault` panic). Left: the
code size, `CostsV86` and `LimitsV86`. -/
theorem ftMetadata_refines_all (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (st : Option WNear.State) (ctx : Context)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "ft_metadata") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .ftMetadata
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .ftMetadata ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftMetadata) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .ftMetadata) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  cases st with
  | none => exact ftMetadata_refines_uninit cfg size codeOf raw ctx hp hwf hrep hm hc hl hsize
  | some S => exact ftMetadata_refines_init cfg size codeOf raw ctx S hp hwf hrep hm hc hl hsize

end WNear.Binary.FtMetadataMethod
