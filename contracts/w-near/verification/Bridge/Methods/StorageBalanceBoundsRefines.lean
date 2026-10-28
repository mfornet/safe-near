import Bridge.Methods.StorageBalanceBoundsUninit
import Bridge.Methods.StorageMinimumBalanceRefines

/-!
# `storage_balance_bounds` (306) refines the model

The model's side of `storageBalanceBounds_refines`, as for `storage_minimum_balance`
(`StorageMinimumBalanceRefines`):

* `boundsJ_eq`: the binary returns `{"min":"N","max":"N"}` for `N = minS S`, the JSON of the
  model's `StorageBalanceBounds { min := storageMin, max := some storageMin }`
  (`usage_of_header`: `minS S` is `storageMin` on a well-formed state).
* `hag_wnear`: the model's step agrees with every final host.
* `cost_le`, `hbound_wnear`: the model's gas bound (`gas_306`: `computeGas`, the trie nodes and
  97 bytes of return data) covers loading and the method's cost under `CostsV86`. No new
  premise: the cost is at most 40000 `regular_op_cost`s, eight linear-op charges and the host
  calls' (the second `to_string` allocates on a free list of three cells, `costAllocF cfg 3`:
  1930 `regular_op_cost`s against 940).
* `readOk_of`, `pre_of_ctx`: the host reads the model state, from the context (`LimitsV86`).
* `storageBalanceBounds_refines_init`, and `storageBalanceBounds_refines_all` on any storage
  the model represents.
-/

namespace WNear.Binary.StorageBalanceBoundsMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface ContractModel WNear.Binary
open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.StorageBalanceBoundsBody
  WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.StorageMinimumBalance (minS)

/-! ## The model's step and the returned JSON -/

/-- The model's step for `storage_balance_bounds` on the state `S`. -/
theorem step_eq (cfg : WNear.Config) (ctx : Context) (S : WNear.State) :
    (WNear.wnear cfg).step ctx (some S) .storageBalanceBounds =
      if 0 < deficit ctx S then .error { failure := .lackBalanceForState (deficit ctx S), logs := [] }
      else .ok { state := S, ret := .storageBalanceBounds S.storageBalanceBounds, logs := [], promises := [] } := by
  rfl

theorem utf8_append (a b : String) : (a ++ b).toUTF8.toList = a.toUTF8.toList ++ b.toUTF8.toList := by
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray,
    String.toByteArray_append, ToVec.toList_eq, ToVec.toList_eq, ToVec.toList_eq]
  simp [ByteArray.data_append]

/-- An ASCII literal's bytes. -/
theorem lit_bytes (s : String) (l : List Char) (bs : List UInt8) (hs : s = String.ofList l)
    (h : ∀ c ∈ l, c.val ≤ 127) (hb : l.map (fun c => c.toUInt8) = bs) : s.toUTF8.toList = bs := by
  subst hs hb
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode, ToVec.flat_ascii _ h, ToVec.toList_eq]
  simp

theorem lit_min : ("{\"min\":" : String).toUTF8.toList = [123, 34, 109, 105, 110, 34, 58] :=
  lit_bytes _ ['{', '"', 'm', 'i', 'n', '"', ':'] _ rfl (by decide) rfl
theorem lit_max : (",\"max\":" : String).toUTF8.toList = [44, 34, 109, 97, 120, 34, 58] :=
  lit_bytes _ [',', '"', 'm', 'a', 'x', '"', ':'] _ rfl (by decide) rfl
theorem lit_end : ("}" : String).toUTF8.toList = [125] := lit_bytes _ ['}'] _ rfl (by decide) rfl

theorem minS_eq {S S' : WNear.State} (hS' : S'.WF) (h : WNear.header S = WNear.header S') : minS S = S'.storageMin := by
  rw [minS, StorageMinimumBalanceMethod.usage_of_header hS' h]; rfl

/-- The model's JSON of `{ min: m, max: Some(m) }`, as bytes. -/
theorem retBytes_eq (m : Nat) :
    (WNear.Ret.storageBalanceBounds { min := m, max := some m }).json.toUTF8.toList =
      [123, 34, 109, 105, 110, 34, 58] ++ jsonOf m ++ [44, 34, 109, 97, 120, 34, 58] ++ jsonOf m ++ [125] := by
  show ("{\"min\":" ++ WNear.jsonU128 m ++ ",\"max\":" ++ WNear.jsonU128 m ++ "}").toUTF8.toList = _
  rw [utf8_append, utf8_append, utf8_append, utf8_append, lit_min, lit_max, lit_end, jsonU128_bytes]

theorem boundsJson_eq (m : Nat) :
    SerdeStruct.boundsJson m m =
      [123, 34, 109, 105, 110, 34, 58] ++ jsonOf m ++ [44, 34, 109, 97, 120, 34, 58] ++ jsonOf m ++ [125] := by
  simp only [SerdeStruct.boundsJson, SerdeStruct.jstr, SerdeStruct.keyMin, SerdeStruct.keyMax, jsonOf,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The binary's return bytes are the model's. -/
theorem boundsJ_eq {S S' : WNear.State} (hS' : S'.WF) (h : WNear.header S = WNear.header S') :
    boundsJ S = (WNear.Ret.storageBalanceBounds S'.storageBalanceBounds).json.toUTF8.toList := by
  rw [boundsJ, minS_eq hS' h, boundsJson_eq]
  exact (retBytes_eq _).symm

/-! ## The final host -/

theorem post_field {α : Type} (f : NearState → α) (hf : ∀ x, f (erase x) = f x)
    (hsel : ∀ x b, f (x.selectReturnValue b) = f x) (hreg : ∀ x i v, f (x.setRegister i v) = f x)
    (hacc : ∀ x a, f { x with storageAccounting := a } = f x)
    {S : WNear.State} {h0 e : NearState} (hp : post S h0 e) : f e = f h0 := by
  obtain ⟨st, h1, -, ⟨s2, -, he⟩, rfl⟩ := hp
  rw [hf, hsel, erase_field he f hf]
  unfold storageReadRegs
  split
  · split
    · exact hacc _ _
    · rw [hreg]; exact hacc _ _
  · exact hacc _ _

theorem post_returnData {S : WNear.State} {h0 e : NearState} (hp : post S h0 e) :
    e.returnData = some (boundsJ S) := by
  obtain ⟨st, h1, -, -, rfl⟩ := hp
  rfl

open WNear in
/-- **`hag` for `storage_balance_bounds`**: as `StorageMinimumBalanceMethod.hag_wnear`, the
return data the JSON of the bounds. -/
theorem hag_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (h0 : NearState) (hh0 : eraseP h0 = eraseP (hostOf ctx raw)) :
    ∀ e, post S h0 e →
      AgreesWith (wnear cfg) ctx raw e ((wnear cfg).step ctx st .storageBalanceBounds) := by
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
      · show returnOf e = .value (WNear.Ret.storageBalanceBounds S'.storageBalanceBounds).json.toUTF8.toList
        rw [returnOf, post_returnData hp, boundsJ_eq hinv.toWF hhd]
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

theorem pages_newCap' (lo hi : UInt64) :
    (AllocNewCell.cellPages (AllocAlloc.wordsOf (FmtGrow.newCap 0 (FmtString.kOf (FmtU128.val lo hi)))) 1).toNat
      ≤ 1 := by
  have hk := FmtString.kOf_toNat lo hi
  have hd := FmtString.decDigits_le lo hi
  have hp := pages_newCap ⟨(FmtString.kOf (FmtU128.val lo hi)).toNat, by omega⟩
  simpa only [UInt32.ofNat_toNat] using hp

/-- `costAllocF` on a free list of three cells, one page at most. -/
theorem cAlloc3 (s : UInt32) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf s) 1).toNat ≤ 1) :
    VecWithCap.costAllocF cfg 3 s ≤ 1930 * c + L := by
  have := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
  simp only [VecWithCap.costAllocF, show ¬ (3 ≤ 2) by decide, ite_false, AllocWalk.cost310W, AllocWalk.walkCost,
    AllocWalk.wc]
  omega

/-- `costAllocF` on at most two cells or three, one page at most. -/
theorem cAllocLe (F : Nat) (hF : F ≤ 3) (s : UInt32)
    (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf s) 1).toNat ≤ 1) :
    VecWithCap.costAllocF cfg F s ≤ 1930 * c + L := by
  by_cases h2 : F ≤ 2
  · rw [VecWithCap.costAllocF_le2 cfg h2]
    have := cAllocF cfg s hp
    omega
  · rw [show F = 3 by omega]; exact cAlloc3 cfg s hp

theorem c385 (F : Nat) (hF : F ≤ 3) (lo hi : UInt64) : ToString.cost385 cfg F lo hi ≤ 9165 * c + L := by
  have hk := FmtString.kOf_toNat lo hi
  have hd := FmtString.decDigits_le lo hi
  have h1 := cAllocLe cfg F hF _ (pages_newCap' lo hi)
  have h2 := Nat.mul_le_mul_right c (fmt_le lo hi)
  have h3 := Nat.mul_le_mul_right c (memcpy_le (FmtString.kOf (FmtU128.val lo hi)).toNat)
  have h4 := act759 c
  have h6 := act872 c
  have h7 := act353 c
  have h5 : (18 * (FmtString.kOf (FmtU128.val lo hi)).toNat + 6) * c ≤ 708 * c :=
    Nat.mul_le_mul_right _ (by omega)
  have h8 : SerializeStr.cost383 (FmtString.kOf (FmtU128.val lo hi)).toNat * c ≤ 2648 * c := by
    apply Nat.mul_le_mul_right
    have := memcpy_le (FmtString.kOf (FmtU128.val lo hi)).toNat
    simp only [SerializeStr.cost383, SerializeStr.cost344, show MemCpy.cost 1 = 24 by rfl]
    omega
  simp only [ToString.cost385, FmtString.cost746, FmtString.cost872, FmtString.cost353, FmtString.costGrow,
    show MemCpy.cost 0 = 4 by rfl]
  omega

theorem c108 (lo hi : UInt64) : SerdeStruct.cost108 cfg 2 lo hi lo hi ≤ 23000 * c + 2 * L := by
  have a := c385 cfg 2 (by decide) lo hi
  have b := c385 cfg 3 (by decide) lo hi
  have h3 : SerializeStr.cost383 3 = 848 := by rfl
  simp only [SerdeStruct.cost108, h3, show MemCpy.cost 1 = 24 by rfl, show 2 + 1 = 3 by rfl]
  omega

theorem cM306 (h : NearState) (S : WNear.State) :
    costM306 cfg h S ≤ 26000 * c + 3 * L + cost219 cfg h S := by
  have a := c108 cfg (loN S) (hiN S)
  have b := cAllocF cfg 128 pages_fixed.2.2
  simp only [costM306, StorageBalanceBounds.cost418, VecWithCap.costAllocF_le2 cfg (show 2 ≤ 2 by decide)]
  omega

end Gas

/-- The arithmetic of `cost_le`, for the returned bytes `j`. -/
theorem cost_le_gen (rc : RuntimeConfig) (h : NearState) (S : WNear.State)
    (j : List UInt8) (hv : h.storage WNear.stateKey = some (WNear.header S)) :
    10 * rc.wasm.regularOpCost + (477 * rc.wasm.regularOpCost + costM306 rc.wasm h S + 1010 * rc.wasm.regularOpCost +
      valueReturnUse h j.length) ≤
      40000 * rc.wasm.regularOpCost + 8 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h j.length +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h j.length := by
  have a := cM306 rc.wasm h S
  have b := c161 rc.wasm
  have d := c687 rc.wasm
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
    cost rc S h ≤ 40000 * rc.wasm.regularOpCost + 8 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h (boundsJ S).length +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h (boundsJ S).length := by
  rw [cost, cost306]
  exact cost_le_gen rc h S _ hv

open NearInterface in
theorem dataGas_le97 (ctx : Context) (raw : RawStorage) (n : Nat) (hn : n ≤ 97) :
    valueReturnDataGas (erase (hostOf ctx raw)) n ≤ returnDataGas ctx 97 := by
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
    have a := Nat.mul_le_mul_left (ctx.protocol.fees.actionFees.newDataReceiptByte.send (decide (r = ctx.current))) hn
    have b := Nat.mul_le_mul_left ctx.protocol.fees.actionFees.newDataReceiptByte.execution hn
    dsimp only at ih
    rw [Nat.add_mul]
    omega

/-- The model's gas bound covers loading and the method's cost. -/
theorem hbound_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (size : Nat)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + cost ctx.protocol S (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .storageBalanceBounds := by
  have hcost := cost_le ctx.protocol (erase (hostOf ctx raw)) S hval
  have htrie := trie_le ctx raw
  have hn := boundsJ_length S
  have hdata := dataGas_le97 ctx raw _ hn
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  have hrm := Nat.mul_le_mul hc.readMemoryByte hn
  simp only [extUse, hx'] at hcost
  rw [gas_306, hl]
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.linearBase; have := hc.linearUnit; have := hc.base
  have := hc.loadingBase; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  omega

/-! ## The host reads the model state -/

/-- A host equal to the initial one up to gas and the recorded proof, with room for the
`STATE` lookup, reads the model state `S` that `STATE` holds (`ReadOkV` for `boundsJ S`). -/
theorem readOk_of (ctx : Context) (raw : RawStorage) (S : WNear.State) (hwf : ctx.WF raw)
    (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie
      (Near.TrieOverlay.lookupProofBound (Near.TrieOverlay.contractKey ctx.current.bytes WNear.stateKey))) :
    ReadOkV h S ctx.trie (boundsJ S) := by
  have hr := FtTotalSupplyMethod.readOk_of ctx raw S hwf hl hval h he hproof
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  refine ⟨hr.value, hr.acc, hr.keyLen, hr.trie, hr.zero, hr.link, hr.proof, hr.regLen, ?_⟩
  have e : (hostOf ctx raw).config.maxReturnLen = some ctx.protocol.wasm.limits.maxLengthReturnedData := rfl
  rw [hcfg, e]
  have := hl.returned
  have := boundsJ_length S
  simpa [withinLimit] using (show (boundsJ S).length ≤ ctx.protocol.wasm.limits.maxLengthReturnedData by omega)

/-- **`hpre` and `hpreP` of `storage_balance_bounds`**, from the context. -/
theorem pre_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (hwf : ctx.WF raw) (hl : LimitsV86 ctx.protocol)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S)) :
    (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .storageBalanceBounds) →
        pre S (erase (hostOf ctx raw))) ∧
      pre S (eraseP (hostOf ctx raw)) := by
  refine ⟨fun hroom => ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩,
    ⟨ctx.trie, readOk_of ctx raw S hwf hl hval _ rfl ?_⟩⟩
  · exact (budget_of_room hwf hroom _ rfl rfl).mono (lookup_le_proofBound ctx)
  · intro size hsz
    cases hsz

/-! ## Refinement -/

/-- **`storage_balance_bounds` refines the model on an initialized contract.** Left: the code
size, `CostsV86` and `LimitsV86`. -/
theorem storageBalanceBounds_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (hm : ctx.method = "storage_balance_bounds") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) .storageBalanceBounds
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) .storageBalanceBounds ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) .storageBalanceBounds) →
      Matches (WNear.wnear cfg) ctx raw r res ∧
        r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) .storageBalanceBounds) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨-, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  obtain ⟨hpre, hpreP⟩ := pre_of_ctx cfg ctx raw (some S) S hwf hl hval
  exact storageBalanceBounds_refines (WNear.wnear cfg) size codeOf raw (some S) ctx .storageBalanceBounds S
    hp hwf hm hpre hpreP
    (hag_wnear cfg ctx raw (some S) S hrep hwf hval _ rfl) (hag_wnear cfg ctx raw (some S) S hrep hwf hval _ rfl)
    (hbound_wnear cfg ctx raw (some S) S size hval hc hsize)

/-- **`storage_balance_bounds` refines the model**: the clauses of `Refines` for a call to it,
on any storage the model represents: an initialized contract or none (the `PanicOnDefault`
panic). Left: the code size, `CostsV86` and `LimitsV86`. -/
theorem storageBalanceBounds_refines_all (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (st : Option WNear.State) (ctx : Context)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "storage_balance_bounds") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .storageBalanceBounds
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .storageBalanceBounds ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .storageBalanceBounds) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .storageBalanceBounds) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  cases st with
  | none => exact storageBalanceBounds_refines_uninit cfg size codeOf raw ctx hp hwf hrep hm hc hl hsize
  | some S => exact storageBalanceBounds_refines_init cfg size codeOf raw ctx S hp hwf hrep hm hc hl hsize

end WNear.Binary.StorageBalanceBoundsMethod
