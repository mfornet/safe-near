import Bridge.Functions.SerdeWeightedTraceCost

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.SerdeObjectMixedTrace
open NearInterface ContractModel in
theorem full_weighted_bundled_plan (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (hcosts : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hnone : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (WasmLogic.bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    BalanceOf297AbsentCall.AbsentParserPlan cfg size raw modelSt ctx S a bs := by
  have hfull : bs.length ≤ 4194304 := by omega
  have hparse := selected_weighted_parser_linear_full ctx.protocol.wasm bs rest N a hlen ho hloop
    hcosts.regularOp hcosts.linearBase hcosts.linearUnit
  have hbudget := BalanceOf297AbsentCall.provider_model_budget_of_parser_linear cfg ctx raw modelSt S a bs
    _ 44 size hcosts hsize hargs hfull (by decide) hparse hv hnone
  exact bundled_provider_plan_weighted cfg ctx raw modelSt S a bs rest N size
    (selectedBundledKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedWeightedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) hfull
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    (fun len _ => Bound.selected_value_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1)
    (fun len _ => Bound.selected_weighted_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_weighted_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    ho hloop hend hbudget

open NearInterface ContractModel in
theorem full_weighted_bundled_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hcosts : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
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
  have hfull : bs.length ≤ 4194304 := by omega
  have hparse := selected_weighted_parser_linear_full ctx.protocol.wasm bs rest N a hlen ho hloop
    hcosts.regularOp hcosts.linearBase hcosts.linearUnit
  exact weighted_linear_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hfull hp hwf hm hl ho hloop hend hcosts hsize hparse hargs hrep ha

end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.ContractModel
open SerdeRead ParseStr

/-- Initialized absent account and successful full object model up to 4194304 bytes.
Escapes and complete nested ignored values are supported; the successful actual parser model and initialized absent-account classification remain explicit. -/
def FullGeneralObjectAbsentCase (st : Option WNear.State) (ctx : Context) (c : WNear.Call) : Prop :=
  ∃ (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat),
    st = some S ∧ c = .ftBalanceOf a ∧ a ∉ S.registered ∧ ctx.args = bs ∧
    bs.length ≤ 4194304 ∧ bs[wsLen bs]? = some 0x7B ∧
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      SerdeIgnObject.ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest) ∧
    bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length

theorem full_general_object_case_accepted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : FullGeneralObjectAbsentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st c
    ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.full_weighted_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hreceipt hp hwf hm hl
    ho hloop hend hc hsize hargs hrep ha).2

theorem full_general_object_case_no_issue (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : FullGeneralObjectAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.full_weighted_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hreceipt hp hwf hm hl
    ho hloop hend hc hsize hargs hrep ha).1

theorem full_general_parser_cost (cfg : WNear.Config) (size : Nat) (raw : RawStorage)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hrep : (WNear.wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hcase : FullGeneralObjectAbsentCase (some S) ctx (.ftBalanceOf a)) :
    ∃ parseGas outF, DeployedParserProvider ctx.protocol ctx.args a parseGas outF ∧
      ProviderModelBudget cfg size raw (some S) ctx S a parseGas outF := by
  obtain ⟨S', a', bs, rest, N, hS, ha', ha, hargs, hlen, ho, hloop, hend⟩ := hcase
  have hSS := Option.some.inj hS
  have haa := WNear.Call.ftBalanceOf.inj ha'
  subst S' a'
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  have hkey := NearDepositMethod.accountKey_ofNear a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hkey
  change WNear.accountKey a = WNear.accountsPrefix ++
    (WasmLogic.bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList) at hkey
  rw [Wasm.ByteEncoding.string_utf8_length] at hkey
  have hnone : (hostOf ctx raw).storage (copiedKey a) = none := by
    have hr := FtBalanceOfMethod.reg_storage ctx raw S hwf hraw (hostOf ctx raw) rfl a
    rw [hkey] at hr
    simpa only [NearDepositMethod.regOf, if_neg ha, Option.map_none] using hr
  have hplan := SerdeObjectPrefix.full_weighted_bundled_plan cfg ctx raw (some S) S a bs rest N size hc hsize hargs hlen ho hloop hend hval hnone
  obtain ⟨parseGas, outF, _, _, hprovider, hbudget⟩ := hplan
  rw [hargs]
  exact ⟨parseGas, outF, hprovider, hbudget⟩

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface.Json WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)

theorem accepted_object_model (bs : List UInt8) (a : WNear.AccountId)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hd : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) :
    ∃ N rest, objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
        (bs.drop (wsLen bs + 1)) = some (some a, rest) ∧
      bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length := by
  have hdv : Agrees (valueAs WNear.account) (valueAs WNear.account) := fun _ => Or.inl rfl
  obtain ⟨r, hs, he⟩ := SerdeFromTrait.decode_struct hdv SerdeIgnObject.ignored_agrees hd
  have hskip := WNear.SerdeStructLoop.skip_drop_of (bs := bs) (x := 0) (by simpa using ho)
  simp only [List.drop_zero, Nat.zero_add] at hskip
  have hsuffix := WNear.JsonSuffix.structDe_suf "account_id" _ _
    (fun _ _ _ h => WNear.JsonSuffix.valueAs_suf _ h)
    (fun bs r h => WNear.JsonSuffix.agrees_suf SerdeIgnObject.ignored_agrees
      (fun _ x _ h => by cases x; exact WNear.JsonSuffix.valueSkip_suf h) bs () r h) hs
  have hr := WNear.JsonSuffix.drop_suf hsuffix
  have hws := SerdeFromTrait.wsLen_all he
  have hlen := hsuffix.length_le
  have hnot : ∀ r', skipWhitespace (bs.drop (wsLen bs + 1)) ≠ 0x7D :: r' := by
    intro r' hx
    rw [structDe_objE "account_id" _ _ hskip hx] at hs
    cases hs
  rw [structDe_objM "account_id" _ _ hskip hnot] at hs
  simp only [Option.bind_eq_some_iff] at hs
  obtain ⟨⟨seen, rest⟩, hloop, hres⟩ := hs
  cases seen with
  | none => simp at hres
  | some a' =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hres
    obtain ⟨rfl, rfl⟩ := hres
    exact ⟨_, rest, hloop, by rw [hr, hws]; omega⟩

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)

theorem account_value_model {bs rest : List UInt8} {i : Nat} {a : WNear.AccountId}
    (h : valueAs WNear.account (bs.drop i) = some (a, rest)) :
    bs[i + wsLen (bs.drop i)]? = some 0x22 ∧
      stringBody (bs.drop (i + wsLen (bs.drop i) + 1)) [] = some (some a.val, rest) := by
  unfold valueAs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, a', hacc, rfl, rfl⟩ := h
  unfold WNear.account at hacc
  simp only [Option.map_eq_some_iff] at hacc
  obtain ⟨na, hna, rfl⟩ := hacc
  cases v with
  | str s =>
    simp only [accountId, string, Option.bind_eq_bind, Option.bind_some] at hna
    split at hna
    · simp only [Option.some.injEq] at hna
      subst hna
      obtain ⟨tail, hskip, hstr⟩ := SerdeAcctHyp.valueR_str hv
      obtain ⟨hq, heq⟩ := WNear.SerdeStructLoop.skip_drop_cons hskip
      exact ⟨hq, by simpa only [heq, WNear.AccountId.ofNear] using hstr⟩
    · simp at hna
  | _ => simp [accountId, string] at hna

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface.Json WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)

theorem accepted_array_case (S : WNear.State) (ctx : NearInterface.Context) (a : WNear.AccountId)
    (bs : List UInt8) (hargs : ctx.args = bs) (ha : a ∉ S.registered)
    (hlen : bs.length ≤ 4194304) (ho : bs[wsLen bs]? = some 0x5B)
    (hd : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) :
    ArrayAbsentCase (some S) ctx (.ftBalanceOf a) := by
  have hdv : Agrees (valueAs WNear.account) (valueAs WNear.account) := fun _ => Or.inl rfl
  obtain ⟨r, hs, he⟩ := SerdeFromTrait.decode_struct hdv SerdeIgnObject.ignored_agrees hd
  have hskip := WNear.SerdeStructLoop.skip_drop_of (bs := bs) (x := 0) (by simpa using ho)
  simp only [List.drop_zero, Nat.zero_add] at hskip
  have hnot : ∀ r', skipWhitespace (bs.drop (wsLen bs + 1)) ≠ 0x5D :: r' := by
    intro r' hx
    rw [structDe_arrE "account_id" _ _ hskip hx] at hs
    cases hs
  rw [structDe_arrM "account_id" _ _ hskip hnot] at hs
  simp only [Option.bind_eq_some_iff] at hs
  obtain ⟨⟨a', rest⟩, hv, hend⟩ := hs
  have hvalue : valueAs WNear.account (bs.drop (wsLen bs + 1)) = some (a', rest) := by
    simpa only [valueAs, valueR_skip] using hv
  unfold arrEnd at hend
  split at hend
  · rename_i tail hclose
    simp only [Option.some.injEq, Prod.mk.injEq] at hend
    obtain ⟨rfl, rfl⟩ := hend
    have hsuffix := WNear.JsonSuffix.valueAs_suf WNear.account hvalue
    have hr := WNear.JsonSuffix.drop_suf' hsuffix
    have hclose' := hclose
    rw [← hr] at hclose'
    obtain ⟨hb, htail⟩ := WNear.SerdeStructLoop.skip_drop_cons hclose'
    obtain ⟨hq, hmodel⟩ := account_value_model hvalue
    have hws := SerdeFromTrait.wsLen_all he
    have hlast := (WNear.JsonSuffix.cons_suf hclose).trans (hsuffix.trans (List.drop_suffix _ bs))
    have hlastlen := hlast.length_le
    have hlastdrop := WNear.JsonSuffix.drop_suf hlast
    refine ⟨S, a', bs, rest, wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)),
      bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1,
      rfl, rfl, ha, hargs, by omega, ho, rfl, hq, hb, rfl, ?_, hmodel⟩
    rw [htail] at he
    have hws' := SerdeFromTrait.wsLen_all he
    simp only [List.length_drop] at hws'
    have hbl := SerdeNextKey.getElem_lt hb
    omega
  · simp at hend

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.Json WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)

theorem accepted_absent_cases (cfg : WNear.Config) (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hm : ctx.method = "ft_balance_of")
    (hp : (WNear.wnear cfg).Parses ctx.method ctx.args (.ftBalanceOf a))
    (ha : a ∉ S.registered) (hlen : ctx.args.length ≤ 4194304) :
    ArrayAbsentCase (some S) ctx (.ftBalanceOf a) ∨
      FullGeneralObjectAbsentCase (some S) ctx (.ftBalanceOf a) := by
  have hd : WNear.Call.decode "ft_balance_of" ctx.args = some (.ftBalanceOf a) := by
    change WNear.Call.decode ctx.method ctx.args = some (.ftBalanceOf a) at hp
    rwa [hm] at hp
  by_cases ho : ctx.args[wsLen ctx.args]? = some 0x7B
  · obtain ⟨N, rest, hloop, hend⟩ := accepted_object_model ctx.args a ho hd
    exact Or.inr ⟨S, a, ctx.args, rest, N, rfl, rfl, ha, rfl, hlen, ho, hloop, hend⟩
  · by_cases harr : ctx.args[wsLen ctx.args]? = some 0x5B
    · exact Or.inl (accepted_array_case S ctx a ctx.args rfl ha hlen harr hd)
    · have hdv : Agrees (valueAs WNear.account) (valueAs WNear.account) := fun _ => Or.inl rfl
      obtain ⟨r, hs, _⟩ := SerdeFromTrait.decode_struct hdv SerdeIgnObject.ignored_agrees hd
      have hobj : ∀ tail, skipWhitespace ctx.args ≠ 0x7B :: tail := by
        intro tail hx
        have hb := (WNear.SerdeStructLoop.skip_drop_cons (bs := ctx.args) (x := 0) (by simpa using hx)).1
        apply ho
        simpa only [List.drop_zero, Nat.zero_add] using hb
      have harr' : ∀ tail, skipWhitespace ctx.args ≠ 0x5B :: tail := by
        intro tail hx
        have hb := (WNear.SerdeStructLoop.skip_drop_cons (bs := ctx.args) (x := 0) (by simpa using hx)).1
        apply harr
        simpa only [List.drop_zero, Nat.zero_add] using hb
      rw [structDe_other "account_id" _ _ hobj harr'] at hs
      cases hs

end WNear.Binary.BalanceOf297AbsentCall
