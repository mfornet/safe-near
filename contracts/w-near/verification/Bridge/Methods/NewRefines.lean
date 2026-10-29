import Bridge.Methods.NewGas
import Bridge.Methods.NewBudget

/-!
# `new` (290) refines the model

* `NewPost.storage`, `NewPost.mem_keys`, `NewPost.usage`: what the success path leaves of the
  storage and the usage: `STATE` holds `newBytes extra`, the dummy record is gone, the usage grew by
  the one record (`5 + 29 + extra`).
* `newBytes_eq_header`: those are the model's `header (newState p)`.
* `agrees_post`: every host `postNew` allows agrees with the model's step (`agrees_new`).
* `newOk_of`: the host at the boundary meets `NewOk`, the context's trie for `st`.
* `new_refines_none`: no deposit, no state: the clauses of `Refines` (`method_refines_callR`).
* `newRefines_all`: the clauses of `Refines` for `new` on any represented storage.
-/

namespace WNear.Binary.NewMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface ContractModel
open WNear.Binary WNear.Binary.NewBody
open WNear.Binary.MeasureUsage (mKey mVal)
open WNear.Binary.StorageWrite (evictedRegister)
open WNear.Binary.FtTotalSupplyMethod (LimitsV86 budget_of_room CostsV86)
open WNear.Binary.EnvGetters (depLo depHi depLo_or_depHi_eq_zero)
open WNear.Binary.NewGas (hostOf_empty_storage hbound_new)
open Near.TrieOverlay

/-! ## What the success path leaves -/

theorem storageWriteHost_usage (e : Nat) (x : NearState) (k v : List UInt8) (r : UInt64) (s : Near.TrieOverlay.State) :
    (storageWriteHost e x k v r s).context.storageUsage =
      UInt64.ofNat (writeUsage e k v (x.storage k) x.context.storageUsage.toNat) := by
  unfold storageWriteHost logWrite; rfl

theorem storageRemoveHost_usage (e : Nat) (x : NearState) (k : List UInt8) (r : UInt64) (s : Near.TrieOverlay.State) :
    (storageRemoveHost e x k r s).context.storageUsage =
      UInt64.ofNat (removeUsage e k (x.storage k) x.context.storageUsage.toNat) := by
  unfold storageRemoveHost logRemove; rfl

theorem storageWriteHost_keys (e : Nat) (x : NearState) (k v : List UInt8) (r : UInt64) (s : Near.TrieOverlay.State) :
    k ∈ (storageWriteHost e x k v r s).storageKeys := by
  unfold storageWriteHost logWrite
  simp only [NearState.invalidateIterators, NearState.setStorage]
  split
  · rename_i hc
    simpa using hc
  · simp

theorem NewPost.storage {x : Nat} {e0 h4 : NearState} (hp : NewPost x e0 h4) (k : List UInt8) :
    h4.storage k =
      if k = StateRead.stateKey then some (newBytes x) else if k = mKey then none else e0.storage k := by
  obtain ⟨h2, h1, h3, s2, s1, s3, s4, e2, e1, e3, e4⟩ := hp
  rw [erase_field e4 NearState.storage fun _ => rfl, storageWriteHost_storage]
  by_cases hk : k = StateRead.stateKey
  · simp [hk]
  · simp only [hk, ite_false]
    rw [storage_after404 e1 e3, erase_field e2 NearState.storage fun _ => rfl]

theorem NewPost.mem_keys {x : Nat} {e0 h4 : NearState} (hp : NewPost x e0 h4) :
    StateRead.stateKey ∈ h4.storageKeys := by
  obtain ⟨h2, h1, h3, s2, s1, s3, s4, e2, e1, e3, e4⟩ := hp
  rw [erase_field e4 NearState.storageKeys fun _ => rfl]
  exact storageWriteHost_keys _ _ _ _ _ _

theorem newBytes_length (x : Nat) : (newBytes x).length = 29 := by
  simp [newBytes, StateWrite.stateBytes, bytes32]

theorem NewPost.usage {x : Nat} {e0 h4 : NearState} (hp : NewPost x e0 h4)
    (hU : e0.context.storageUsage.toNat + (85 + x) < 2 ^ 64) (hM : e0.storage mKey = none)
    (hS : e0.storage StateRead.stateKey = none) :
    h4.context.storageUsage.toNat = e0.context.storageUsage.toNat + (34 + x) := by
  obtain ⟨h2, h1, h3, s2, s1, s3, s4, e2, e1, e3, e4⟩ := hp
  have u2 : h2.context.storageUsage = e0.context.storageUsage :=
    erase_field e2 (fun y : NearState => y.context.storageUsage) fun _ => rfl
  have st2 : h2.storage = e0.storage := erase_field e2 NearState.storage fun _ => rfl
  have u1 := (erase_field e1 (fun y : NearState => y.context.storageUsage) fun _ => rfl).trans
    (storageWriteHost_usage _ _ _ _ _ _)
  have st1 : h1.storage mKey = some mVal := by
    rw [erase_field e1 NearState.storage fun _ => rfl, storageWriteHost_storage]; simp
  have u3 := (erase_field e3 (fun y : NearState => y.context.storageUsage) fun _ => rfl).trans
    (storageRemoveHost_usage _ _ _ _ _)
  have st3 : h3.storage StateRead.stateKey = none := by
    rw [storage_after404 e1 e3, if_neg stateKey_ne_mKey, st2, hS]
  have u4 := (erase_field e4 (fun y : NearState => y.context.storageUsage) fun _ => rfl).trans
    (storageWriteHost_usage _ _ _ _ _ _)
  rw [st2, hM, u2] at u1
  rw [st1, u1] at u3
  rw [st3, u3] at u4
  rw [u4]
  simp only [writeUsage, removeUsage, MeasureUsage.mKey_length, MeasureUsage.mVal_length, newBytes_length,
    StateRead.stateKey, UInt64.toNat_ofNat] at *
  generalize e0.context.storageUsage.toNat = u at *
  have k1 : (UInt64.ofNat (u + 69 + 16 + x)).toNat = u + 69 + 16 + x := by simp; omega
  rw [k1, show u + 69 + 16 + x - (69 + 16 + x) = u by omega] at *
  have k2 : (UInt64.ofNat u).toNat = u := by simp; omega
  rw [k2]
  simp; omega

/-! ## Against the model -/

theorem storeBytes_u64 (n : Nat) (hn : n < 2 ^ 64) :
    storeBytes (.i64 (UInt64.ofNat n)) 8 = NearSdk.Borsh.leBytes 8 n := by
  have h1 : (UInt64.ofNat n).toNat = n := by simp; omega
  simp only [storeBytes, storeRaw, h1, NearSdk.Borsh.leBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, Nat.shiftRight_eq_div_pow]
  simp only [Nat.div_div_eq_div_mul, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    (apply UInt8.toNat.inj; simp; try omega)

/-- **The bytes `new` stores under `STATE` are the model's `header`** of its state. -/
theorem newBytes_eq_header (p : RuntimeConfig) (hp : 85 + p.fees.numExtraBytesRecord < 2 ^ 64) :
    newBytes p.fees.numExtraBytesRecord = WNear.header (newState p) := by
  rw [StateReadModel.header_eq]
  simp only [newBytes, newState, WNear.new, WNear.Config.measuredAccountStorageUsage,
    WNear.Config.accountEntryBytes, WNear.Config.ofRuntime, WNear.maxAccountIdBytes,
    storeBytes_u64 _ (by omega : 1 + 4 + 64 + 16 + p.fees.numExtraBytesRecord < 2 ^ 64)]
  have ha : WNear.accountsPrefix = [97] := by decide +kernel
  simp only [StateWrite.stateBytes, StateRead.stateBytes, NearSdk.Borsh.u64, ha, List.append_assoc]
  rfl

/-- The host a call starts from, as the success path needs it: no storage, the usage, the
balance, no logs, no return data, no promises. -/
structure Start (ctx : Context) (e0 : NearState) : Prop where
  storage : ∀ k, e0.storage k = none
  usage : e0.context.storageUsage.toNat = ctx.storageUsage
  balance : e0.context.accountBalance = ctx.balance + ctx.attached
  logs : e0.logs = []
  ret : e0.returnData = none
  promises : NoPromises e0

theorem start_erase (ctx : Context) (hwf : ctx.WF ∅) : Start ctx (erase (hostOf ctx ∅)) := by
  have hlt : ctx.storageUsage < 2 ^ 64 := by have := hwf.usage_room; omega
  refine ⟨hostOf_empty_storage ctx, ?_, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩
  show (UInt64.ofNat ctx.storageUsage).toNat = ctx.storageUsage
  simp; omega

theorem start_eraseP (ctx : Context) (hwf : ctx.WF ∅) : Start ctx (eraseP (hostOf ctx ∅)) := by
  have hs := start_erase ctx hwf
  exact ⟨hs.storage, hs.usage, hs.balance, hs.logs, hs.ret, ⟨rfl, rfl, rfl⟩⟩

theorem post_noPromises {x : Nat} {e0 e : NearState} (hp : postNew x e0 e) (h0 : NoPromises e0) : NoPromises e := by
  obtain ⟨h4, hp4, rfl⟩ := hp
  have hk := hp4.keep
  exact ⟨(congrArg Keep.promises hk).trans h0.promises, (congrArg Keep.returnedPromise hk).trans h0.returned,
    (congrArg Keep.gasWeights hk).trans h0.weights⟩

/-- **Every host the success path may end with agrees with the model's step.** -/
theorem agrees_post (cfg : WNear.Config) (ctx : Context) (hd : ctx.attached = 0) {e0 e : NearState}
    (h0 : Start ctx e0) (hU : ctx.storageUsage + (85 + ctx.protocol.fees.numExtraBytesRecord) < 2 ^ 64)
    (hp : postNew ctx.protocol.fees.numExtraBytesRecord e0 e) :
    AgreesWith (WNear.wnear cfg) ctx ∅ e ((WNear.wnear cfg).step ctx none .new) := by
  obtain ⟨h4, hp4, rfl⟩ := hp
  have hk := hp4.keep
  apply agrees_new cfg ctx (erase h4) hd
  · show (finalStorage h4).toFinset = _
    rw [encode_new, ← newBytes_eq_header ctx.protocol (by omega), ← StateRead.stateKey_eq]
    ext ⟨k, v⟩
    simp only [finalStorage, List.mem_toFinset, List.mem_filterMap, Option.map_eq_some_iff, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨k', -, v', hv, rfl, rfl⟩
      rw [(NewPost.storage hp4), h0.storage] at hv
      by_cases hk' : k' = StateRead.stateKey
      · simp only [hk', ite_true, Option.some.injEq] at hv
        exact ⟨hk', hv.symm⟩
      · simp only [hk', ite_false] at hv
        split at hv <;> cases hv
    · rintro ⟨rfl, rfl⟩
      refine ⟨StateRead.stateKey, (NewPost.mem_keys hp4), newBytes ctx.protocol.fees.numExtraBytesRecord, ?_, rfl, rfl⟩
      rw [(NewPost.storage hp4)]; simp
  · show h4.context.storageUsage.toNat = _
    rw [NewPost.usage hp4 (by rw [h0.usage]; omega) (h0.storage _) (h0.storage _), h0.usage]
  · exact (congrArg Keep.balance hk).trans h0.balance
  · exact (congrArg Keep.logs hk).trans h0.logs
  · exact (congrArg Keep.returnData hk).trans h0.ret

/-! ## The host at the boundary -/

/-- A host equal to the initial one up to gas and the recorded proof, with no deposit and no
storage, meets `NewOk` with the context's trie, given room in the recorded proof. -/
theorem newOk_of (ctx : Context) (hwf : ctx.WF ∅) (hl : LimitsV86 ctx.protocol) (hcn : CostsNewV86 ctx.protocol)
    (hd : ctx.attached = 0) (h : NearState) (he : eraseP h = eraseP (hostOf ctx ∅))
    (hproof : ProofBudget h ctx.trie
      (lookupProofBound (contractKey ctx.current.bytes StateRead.stateKey) +
        (writeProofCost (contractKey ctx.current.bytes mKey) none +
          removeProofCost (contractKey ctx.current.bytes mKey) (some mVal)) +
        writeProofCost (contractKey ctx.current.bytes StateRead.stateKey) none)) :
    NewOk ctx.protocol.fees.numExtraBytesRecord h ctx.trie := by
  have hsto : h.storage = (hostOf ctx ∅).storage := eraseP_field he NearState.storage fun _ => rfl
  have hacc : h.storageAccounting = some ctx.trie :=
    eraseP_field he NearState.storageAccounting fun _ => rfl
  have hcfg : h.config = (hostOf ctx ∅).config := eraseP_field he NearState.config fun _ => rfl
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x => x.context.currentAccountId) fun _ => rfl
  have hatt : h.context.attachedDeposit = ctx.attached :=
    eraseP_field he (fun x => x.context.attachedDeposit) fun _ => rfl
  have hus : h.context.storageUsage = (hostOf ctx ∅).context.storageUsage :=
    eraseP_field he (fun x => x.context.storageUsage) fun _ => rfl
  have hkey : (hostOf ctx ∅).config.maxStorageKeyLen = some ctx.protocol.wasm.limits.maxLengthStorageKey := rfl
  have hval : (hostOf ctx ∅).config.maxStorageValueLen = some ctx.protocol.wasm.limits.maxLengthStorageValue := rfl
  have hreg : (hostOf ctx ∅).config.maxRegisterLen = some ctx.protocol.wasm.limits.maxRegisterSize := rfl
  have := hl.storageKey; have := hl.register; have := hcn.storageValue
  refine ⟨eraseP_field he (fun x => x.context.isView) fun _ => rfl, ?_, ?_, ?_, hacc,
    ⟨hwf.trie_canonical, hwf.trie_no_zero_hash⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [depLo_or_depHi_eq_zero, hatt, hd, Nat.zero_mod]
  · rw [hsto]; exact hostOf_empty_storage ctx _
  · rw [hsto]; exact hostOf_empty_storage ctx _
  · intro k
    rw [hsto, hid]
    exact hostOf_storage_view ctx ∅ hwf k
  · rw [hid]; exact hproof
  · rw [hcfg, hkey]; simpa [withinLimit] using (show 5 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey by omega)
  · rw [hcfg, hkey]; simpa [withinLimit] using (show 69 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey by omega)
  · rw [hcfg, hval]; simpa [withinLimit] using (show 16 ≤ ctx.protocol.wasm.limits.maxLengthStorageValue by omega)
  · rw [hcfg, hval]; simpa [withinLimit] using (show 29 ≤ ctx.protocol.wasm.limits.maxLengthStorageValue by omega)
  · rw [hcfg, hreg]; simpa [withinLimit] using (show 16 ≤ ctx.protocol.wasm.limits.maxRegisterSize by omega)
  · rw [hus]
    have := hwf.usage_room; have := hcn.usageRoom
    show (UInt64.ofNat ctx.storageUsage).toNat + _ < _
    simp; omega

/-- The four storage calls fit the model's `proofBound`. -/
theorem proof_le (ctx : Context) :
    lookupProofBound (contractKey ctx.current.bytes StateRead.stateKey) +
        (writeProofCost (contractKey ctx.current.bytes mKey) none +
          removeProofCost (contractKey ctx.current.bytes mKey) (some mVal)) +
        writeProofCost (contractKey ctx.current.bytes StateRead.stateKey) none ≤ WNear.proofBound ctx := by
  have h := proof_new_le ctx mVal MeasureUsage.mVal_length
  rw [show dummyKey = mKey by decide, ← StateRead.stateKey_eq] at h
  omega

/-! ## The clauses of `Refines` -/

set_option maxRecDepth 100000 in
/-- **`new` refines the model on an uninitialized contract with no deposit**: the binary stores
the model's `new` state (or the account cannot pay for it, as the model says). -/
theorem new_refines_none (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none) (hm : ctx.method = "new")
    (hd : ctx.attached = 0) (hc : CostsV86 ctx.protocol) (hcn : CostsNewV86 ctx.protocol)
    (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none .new
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none .new ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none .new) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none .new) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  subst hraw
  have hU : ctx.storageUsage + (85 + ctx.protocol.fees.numExtraBytesRecord) < 2 ^ 64 := by
    have := hwf.usage_room; have := hcn.usageRoom; omega
  exact method_refines_callR (WNear.wnear cfg) size codeOf ∅ none ctx .new
    (preNew ctx.protocol.fees.numExtraBytesRecord) (costNew ctx.protocol)
    (postNew ctx.protocol.fees.numExtraBytesRecord) hp hwf (by rw [hm]; decide)
    (by rw [hm]; exact export_290) funcType_290 (by decide) (by decide) (new_runs ctx.protocol)
    (fun hroom => ⟨ctx.trie, newOk_of ctx hwf hl hcn hd _ rfl
      ((budget_of_room hwf hroom _ rfl rfl).mono (proof_le ctx))⟩)
    ⟨ctx.trie, newOk_of ctx hwf hl hcn hd _ rfl (by intro size hsz; cases hsz)⟩
    (fun e he => post_noPromises he (start_erase ctx hwf).promises)
    (fun e he => post_noPromises he (start_eraseP ctx hwf).promises)
    (fun e he => agrees_post cfg ctx hd (start_erase ctx hwf) hU he)
    (fun e he => agrees_post cfg ctx hd (start_eraseP ctx hwf) hU he)
    (hbound_new cfg ctx size hc hcn hsize)

/-- **`new` refines the model** on any represented storage: the clauses of `Refines` for a call
to `new` (function 290). -/
theorem newRefines_all (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (st : Option WNear.State) (ctx : Context)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "new") (hc : CostsV86 ctx.protocol) (hcn : CostsNewV86 ctx.protocol)
    (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .new
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .new ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .new) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .new) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  by_cases hd : ctx.attached = 0
  · cases st with
    | none => exact new_refines_none cfg size codeOf raw ctx hp hwf hrep hm hd hc hcn hl hsize
    | some S => exact new_refines_init cfg size codeOf raw ctx S hp hwf hrep hm hd hc hcn hl hsize
  · exact new_refines_deposit cfg size codeOf raw ctx st hp hwf hrep hm hd hc hl hsize

end WNear.Binary.NewMethod
