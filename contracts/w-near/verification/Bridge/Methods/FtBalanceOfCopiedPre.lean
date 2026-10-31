import Bridge.Methods.FtBalanceOfCopiedModel

/-! Instantiate the copied absent case from a well-formed represented context.
The final theorem covers this specific input/account branch, not all balance calls. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface in
set_option maxRecDepth 100000 in
theorem copied_entry_pre_of (ctx : Context) (raw : RawStorage) (S : WNear.State) (a : WNear.AccountId)
    (bs : List UInt8) (hwf : ctx.WF raw) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (hnone : (hostOf ctx raw).storage (copiedKey a) = none)
    (h : NearState) (he : eraseP h = eraseP (hostOf ctx raw))
    (hproof : ProofBudget h ctx.trie (WNear.proofBound ctx)) :
    CopiedAbsentPre S a bs ctx.trie (WNear.proofBound ctx) h := by
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
    absent := by rw [hsto]; exact hnone
    registerLimit := hlim NearConfig.maxRegisterLen 29 _ rfl (by have := hl.register; omega)
    returnLimit := hlim NearConfig.maxReturnLen 3 _ rfl (by have := hl.returned; omega) }
  · intro key
    rw [hsto, hid]
    exact hostOf_storage_view ctx raw hwf key
  · rw [hsto, hval, hnone]
    simp only [readProofCost, Option.map_some, Option.getD_some, Option.map_none, Option.getD_none,
      StateReadModel.header_length, Nat.add_zero]
    unfold WNear.proofBound
    simp only [WNear.storageAccesses, WNear.maxStorageValueBytes, WNear.storageRemovals]
    omega

open NearInterface in
theorem copied_entry_at_of_ctx (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (hwf : ctx.WF raw) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (hnone : (hostOf ctx raw).storage (copiedKey a) = none) :
    CopiedEntryAt cfg ctx raw modelSt S a bs ctx.trie (WNear.proofBound ctx) := by
  refine ⟨fun hroom => copied_entry_pre_of ctx raw S a bs hwf hl hargs hlen hval hnone _ rfl ?_,
    copied_entry_pre_of ctx raw S a bs hwf hl hargs hlen hval hnone _ rfl ?_⟩
  · exact FtTotalSupplyMethod.budget_of_room hwf hroom _ rfl rfl
  · intro size hsz
    cases hsz

open NearInterface ContractModel in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem copied_array_absent_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∉ S.registered) :
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
  have hkey := NearDepositMethod.accountKey_ofNear a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hkey
  change WNear.accountKey a = WNear.accountsPrefix ++
    (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList) at hkey
  rw [Wasm.ByteEncoding.string_utf8_length] at hkey
  have hnone : (hostOf ctx raw).storage (copiedKey a) = none := by
    have hr := FtBalanceOfMethod.reg_storage ctx raw S hwf hraw (hostOf ctx raw) rfl a
    rw [hkey] at hr
    simpa only [NearDepositMethod.regOf, if_neg ha, Option.map_none] using hr
  have hentry := copied_entry_at_of_ctx cfg ctx raw (some S) S a bs hwf hl hargs hlen hval hnone
  exact copied_array_absent_refines_v86 cfg size codeOf raw (some S) ctx S a bs rest j k ctx.trie
    (WNear.proofBound ctx) hp hwf hm hc hsize hlen ho hj hq he hk hend hmodel hcopied hentry hrep

end WNear.Binary.BalanceOf297AbsentCall
