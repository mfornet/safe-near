import Bridge.Methods.FtBalanceOfPresentAdequacy

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall (storage_read_post_field funcType_297 export_297)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
theorem present_post_field {α : Type} (f : NearState → α) (hf : ∀ x, f (erase x) = f x)
    (hsel : ∀ x b, f (x.selectReturnValue b) = f x) (hreg : ∀ x i v, f (x.setRegister i v) = f x)
    (hacc : ∀ x a, f { x with storageAccounting := a } = f x)
    {a : WNear.AccountId} {lo hi : UInt64} {tr : Near.TrieOverlay.State} {e e' : NearState}
    (hp : presentMethodPost a lo hi tr e e') : f e' = f e := by
  obtain ⟨h1, st1, h2, hs1, hs2, rfl⟩ := hp
  rw [hf, hsel, storage_read_post_field f hf hreg hacc hs2, storage_read_post_field f hf hreg hacc hs1]
  unfold inputHost
  split
  · rfl
  · exact hreg _ _ _

theorem present_post_noPromises {a : WNear.AccountId} {lo hi : UInt64} {tr : Near.TrieOverlay.State} {e e' : NearState}
    (hp : presentMethodPost a lo hi tr e e') (hn : NoPromises e) : NoPromises e' := by
  have hpr := present_post_field NearState.promises (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ => rfl) hp
  have hgw := present_post_field NearState.gasWeights (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ => rfl) hp
  refine ⟨hpr.trans hn.promises, ?_, hgw.trans hn.weights⟩
  obtain ⟨h1, st1, h2, _, _, rfl⟩ := hp
  rfl

/-- Remaining caller obligation: instantiate the concrete host/trie precondition with and without recorded proof. -/
def PresentEntryAt (cfg : WNear.Config) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8)
    (tr : Near.TrieOverlay.State) (bud : Nat) : Prop :=
  (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
    PresentPre S a lo hi bs tr bud (erase (hostOf ctx raw))) ∧
    PresentPre S a lo hi bs tr bud (eraseP (hostOf ctx raw))

/-- Remaining caller obligation: the actual two-read/zero-return postcondition agrees with the model. -/
def PresentAgreement (cfg : WNear.Config) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (modelSt : Option WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (tr : Near.TrieOverlay.State) (e0 : NearState) : Prop :=
  ∀ e, presentMethodPost a lo hi tr e0 e →
    AgreesWith (WNear.wnear cfg) ctx raw e ((WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a))

open NearInterface ContractModel in
/-- The original model allowance must cover actual loading, activation and provider-based body costs. -/
noncomputable def PresentProviderModelBudget (cfg : WNear.Config) (size : Nat) (raw : RawStorage)
    (modelSt : Option WNear.State) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (lo hi : UInt64) (parseGas outF : Nat) : Prop :=
  chargesUse (hostOf ctx raw) (loadingCharges size) +
    presentProviderMethodCost ctx.protocol S a lo hi parseGas outF (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_present_refines_with_obligations (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8) (parseGas outF : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of")
    (hlen : bs.length < 2 ^ 24)
    (hpos : 0 < bs.length)
    (hProvider : PresentDeployedParserProvider ctx.protocol bs a parseGas outF)
    (hBudget : PresentProviderModelBudget cfg size raw modelSt ctx S a lo hi parseGas outF)
    (hentry : PresentEntryAt cfg ctx raw modelSt S a lo hi bs tr bud)
    (hag : PresentAgreement cfg ctx raw modelSt a lo hi tr (erase (hostOf ctx raw)))
    (hagP : PresentAgreement cfg ctx raw modelSt a lo hi tr (eraseP (hostOf ctx raw))) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact method_refines_callR (WNear.wnear cfg) size codeOf raw modelSt ctx (.ftBalanceOf a)
    (PresentPre S a lo hi bs tr bud) (presentProviderMethodCost ctx.protocol S a lo hi parseGas outF) (presentMethodPost a lo hi tr)
    hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_297) funcType_297 (by decide) (by decide)
    (provider_present_runs ctx.protocol S a lo hi bs parseGas outF tr bud hlen hpos hProvider)
    hentry.1 hentry.2
    (fun e he => present_post_noPromises (e := erase (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    (fun e he => present_post_noPromises (e := eraseP (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    hag hagP hBudget


end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall (copiedKey)
open WNear.Binary.U128From (u128Bytes)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
open NearInterface in
set_option maxRecDepth 100000 in
theorem present_entry_pre_of (ctx : Context) (raw : RawStorage) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64)
    (bs : List UInt8) (hwf : ctx.WF raw) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (hsome : (hostOf ctx raw).storage (copiedKey a) = some (u128Bytes lo hi))
    (h : NearState) (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie (WNear.proofBound ctx)) :
    PresentPre S a lo hi bs ctx.trie (WNear.proofBound ctx) h := by
  have hsto : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  have hacc : h.storageAccounting = some ctx.trie := eraseP_field he NearState.storageAccounting fun _ => rfl
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have hinp : h.context.input = ctx.args := eraseP_field he (fun x : NearState => x.context.input) fun _ => rfl
  have hlim : ∀ (f : NearConfig → Option Nat) (n m : Nat), f (hostOf ctx raw).config = some m → n ≤ m →
      withinLimit (f h.config) n = true := by
    intro f n m hf hn
    rw [hcfg, hf]
    simpa [withinLimit] using hn
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hk : (copiedKey a).length ≤ 69 := by
    have hp : WNear.accountsPrefix.length = 1 := by decide +kernel
    simp only [copiedKey, List.length_append, hp, bytes32, List.length_map, List.length_range]
    omega
  have keyBound (key : List UInt8) (hkey : key.length ≤ 69) :
      lookupProofBound (contractKey h.context.currentAccountId key) ≤
        lookupProofBoundLen (2 + ctx.current.bytes.length + WNear.maxStorageKeyBytes) := by
    apply FtTotalSupplyMethod.lookupProofBoundLen_mono
    rw [hid]
    simp only [contractKey, List.length_append, List.length_singleton, WNear.maxStorageKeyBytes,
      WNear.maxAccountIdBytes]
    omega
  have hsbound := keyBound WNear.stateKey (by rw [← StateRead.stateKey_eq]; decide)
  have habound := keyBound (copiedKey a) hk
  refine {
    input := hinp.trans hargs
    inputLimit := hlim NearConfig.maxRegisterLen bs.length _ rfl (by have := hl.register; omega)
    value := by rw [hsto]; exact hval
    accounting := hacc
    keyLimit := hlim NearConfig.maxStorageKeyLen 5 _ rfl (by have := hl.storageKey; omega)
    canonical := ⟨hwf.trie_canonical, hwf.trie_no_zero_hash⟩
    link := ?_
    proof := hproof
    budget := ?_
    accountLimit := hlim NearConfig.maxStorageKeyLen (copiedKey a).length _ rfl (by have := hl.storageKey; omega)
    present := by rw [hsto]; exact hsome
    registerLimit := hlim NearConfig.maxRegisterLen 29 _ rfl (by have := hl.register; omega)
    returnLimit := hlim NearConfig.maxReturnLen (resultLen lo hi).toNat _ rfl (by
      have := hl.returned
      have := resultLen_toNat lo hi
      have := FmtString.decDigits_le lo hi
      omega) }
  · intro key
    rw [hsto, hid]
    exact hostOf_storage_view ctx raw hwf key
  · rw [hsto, hval, hsome]
    simp only [readProofCost, Option.map_some, Option.getD_some, StateReadModel.header_length]
    have hbytes : (u128Bytes lo hi).length = 16 := by simp [u128Bytes, storeBytes]
    rw [hbytes]
    unfold WNear.proofBound
    simp only [WNear.storageAccesses, WNear.maxStorageValueBytes, WNear.storageRemovals]
    omega

open NearInterface in
theorem present_entry_at_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8)
    (hwf : ctx.WF raw) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (hsome : (hostOf ctx raw).storage (copiedKey a) = some (u128Bytes lo hi)) :
    PresentEntryAt cfg ctx raw modelSt S a lo hi bs ctx.trie (WNear.proofBound ctx) := by
  refine ⟨fun hroom => present_entry_pre_of ctx raw S a lo hi bs hwf hl hargs hlen hval hsome _ rfl ?_,
    present_entry_pre_of ctx raw S a lo hi bs hwf hl hargs hlen hval hsome _ rfl ?_⟩
  · exact FtTotalSupplyMethod.budget_of_room hwf hroom _ rfl rfl
  · intro size hsz
    cases hsz


end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall (copiedKey)
open WNear.Binary.U128From (u128Bytes)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
open NearInterface ContractModel WNear WNear.Binary.FtTotalSupplyMethod in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem present_agreement_of_represents (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (tr : Near.TrieOverlay.State) (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (hsome : (hostOf ctx raw).storage (copiedKey a) = some (u128Bytes lo hi))
    (h0 : NearState) (hh0 : eraseP h0 = eraseP (hostOf ctx raw)) :
    ∀ e, presentMethodPost a lo hi tr h0 e →
      AgreesWith (wnear cfg) ctx raw e ((wnear cfg).step ctx st (.ftBalanceOf a)) := by
  intro e hp
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (eraseP x) = f x) → f h0 = f (hostOf ctx raw) :=
    fun f hfe => eraseP_field hh0 f hfe
  -- the represented state
  cases st with
  | none =>
    have h0 : raw = ∅ := hrep
    rw [hostOf_storage, h0] at hval
    simp at hval
  | some S' =>
    obtain ⟨hinv, hraw⟩ := (show Inv cfg S' ∧ raw = encode S' from hrep)
    obtain ⟨reg, hreg, hstep⟩ := FtBalanceOfMethod.account_lookup_and_step cfg ctx raw S' hwf hraw hinv.toWF h0 hh0 a.toNear
    simp only [WNear.AccountId.ofNear_toNear] at hstep
    have hsome0 : h0.storage (copiedKey a) = some (u128Bytes lo hi) := by
      rw [hf NearState.storage (fun _ => rfl)]; exact hsome
    have hlen : a.val.toUTF8.toList.length = a.val.utf8ByteSize := by
      rw [Wasm.ByteEncoding.byteArray_toList_length]; simp [String.toUTF8_eq_toByteArray]
    change h0.storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList)) = _ at hreg
    rw [hlen, hsome0] at hreg
    have hwords : ((reg.map (fun p => p.1.toNat + 2 ^ 64 * p.2.toNat)).getD 0) = FmtU128.val lo hi := by
      cases reg with
      | none => simp at hreg
      | some pair =>
        have hb : u128Bytes pair.1 pair.2 = u128Bytes lo hi := (Option.some.inj hreg).symm
        have hd := congrArg Memory.decodeLE hb
        simpa only [U128From.decodeLE_u128Bytes, FmtU128.val, Option.map_some, Option.getD_some] using hd
    rw [hwords] at hstep
    -- the final host's fields
    have hbal : e.context.accountBalance = ctx.balance + ctx.attached :=
      (present_post_field (fun x => x.context.accountBalance) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.accountBalance) fun _ => rfl)
    have hsu : e.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
      (present_post_field (fun x => x.context.storageUsage) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.storageUsage) fun _ => rfl)
    have hsto : e.storage = (hostOf ctx raw).storage :=
      (present_post_field NearState.storage (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storage fun _ => rfl)
    have hkeys : e.storageKeys = (hostOf ctx raw).storageKeys :=
      (present_post_field NearState.storageKeys (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storageKeys fun _ => rfl)
    have hlogs : e.logs = [] :=
      (present_post_field NearState.logs (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
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
    erw [hstep]
    split
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact hpos, by rw [← hdef]; rfl, ?_⟩
      show [] = logsOf e
      simp [logsOf, hlogs]
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact Nat.eq_zero_of_not_pos hpos, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
      · show returnOf e = .value (WNear.jsonU128 (FmtU128.val lo hi)).toUTF8.toList
        have hd : e.returnData = some ([34] ++ FmtDigits.decDigits (FmtU128.val lo hi) ++ [34]) := by
          obtain ⟨_, _, _, _, _, rfl⟩ := hp; rfl
        rw [returnOf, hd, FtTotalSupplyMethod.jsonU128_bytes]
        rfl
      · show (finalStorage e).toFinset = encode S'
        rw [hfin, finalStorage_hostOf ctx raw hwf.raw_keys_unique, hraw]
      · exact hbal
      · show e.context.storageUsage.toNat = _ - _ + storageUsageOf ctx.protocol (encode S')
        rw [hsuN, ← hraw]
        omega
      · show logsOf e = []
        simp [logsOf, hlogs]

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall (copiedKey)
open WNear.Binary.U128From (u128Bytes)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_present_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8) (parseGas outF : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hlen : bs.length < 2 ^ 24)
    (hpos : 0 < bs.length)
    (hProvider : PresentDeployedParserProvider ctx.protocol bs a parseGas outF)
    (hBudget : PresentProviderModelBudget cfg size raw (some S) ctx S a lo hi parseGas outF)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (hsome : (hostOf ctx raw).storage (copiedKey a) = some (u128Bytes lo hi)) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  have hentry := present_entry_at_of_ctx cfg ctx raw (some S) S a lo hi bs hwf hl hargs hlen hval hsome
  exact provider_present_refines_with_obligations cfg size codeOf raw (some S) ctx S a lo hi bs parseGas outF
    ctx.trie (WNear.proofBound ctx) hp hwf hm hlen hpos hProvider hBudget hentry
    (present_agreement_of_represents cfg ctx raw (some S) S a lo hi ctx.trie hrep hwf hentry.2.value hentry.2.present _ rfl)
    (present_agreement_of_represents cfg ctx raw (some S) S a lo hi ctx.trie hrep hwf hentry.2.value hentry.2.present _ rfl)


end WNear.Binary.BalanceOf297PresentCall
