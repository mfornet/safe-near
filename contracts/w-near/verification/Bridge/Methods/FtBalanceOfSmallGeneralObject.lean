import Bridge.Functions.SerdeTraceCost

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.SerdeObjectMixedTrace
open NearInterface ContractModel in
theorem small_bundled_plan (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (hcosts : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 10000)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hnone : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (WasmLogic.bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    BalanceOf297AbsentCall.AbsentParserPlan cfg size raw modelSt ctx S a bs := by
  have hfull : bs.length ≤ 4194304 := by omega
  have hparse := selected_parser_linear_small ctx.protocol.wasm bs N a rest hlen ho hloop
    hcosts.regularOp hcosts.linearBase hcosts.linearUnit
  have hbudget := BalanceOf297AbsentCall.provider_model_budget_of_parser_linear cfg ctx raw modelSt S a bs
    _ 44 size hcosts hsize hargs hfull (by decide) hparse hv hnone
  exact bundled_provider_plan cfg ctx raw modelSt S a bs rest N size
    (selectedBundledKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) hfull
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    (fun len _ => Bound.selected_value_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1)
    (fun len _ => Bound.selected_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    ho hloop hend hbudget

open NearInterface ContractModel in
theorem small_bundled_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hlen : bs.length ≤ 10000)
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
  have hparse := selected_parser_linear_small ctx.protocol.wasm bs N a rest hlen ho hloop
    hcosts.regularOp hcosts.linearBase hcosts.linearUnit
  exact linear_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hfull hp hwf hm hl ho hloop hend hcosts hsize hparse hargs hrep ha

end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.ContractModel
open SerdeRead ParseStr

/-- Initialized absent account and successful full object model up to 10000 bytes.
Escapes and complete nested ignored values are supported; this classification is a scoped input case. -/
def SmallGeneralObjectAbsentCase (st : Option WNear.State) (ctx : Context) (c : WNear.Call) : Prop :=
  ∃ (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat),
    st = some S ∧ c = .ftBalanceOf a ∧ a ∉ S.registered ∧ ctx.args = bs ∧
    bs.length ≤ 10000 ∧ bs[wsLen bs]? = some 0x7B ∧
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      SerdeIgnObject.ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest) ∧
    bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length

theorem small_general_object_case_accepted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : SmallGeneralObjectAbsentCase st ctx c) :
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
  exact (SerdeObjectPrefix.small_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hreceipt hp hwf hm hl
    ho hloop hend hc hsize hargs hrep ha).2

theorem small_general_object_case_no_issue (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : SmallGeneralObjectAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (SerdeObjectPrefix.small_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hreceipt hp hwf hm hl
    ho hloop hend hc hsize hargs hrep ha).1

theorem small_general_parser_cost (cfg : WNear.Config) (size : Nat) (raw : RawStorage)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hrep : (WNear.wnear cfg).Represents raw (some S)) (hwf : ctx.WF raw)
    (hcase : SmallGeneralObjectAbsentCase (some S) ctx (.ftBalanceOf a)) :
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
  have hplan := SerdeObjectPrefix.small_bundled_plan cfg ctx raw (some S) S a bs rest N size hc hsize hargs hlen ho hloop hend hval hnone
  obtain ⟨parseGas, outF, _, _, hprovider, hbudget⟩ := hplan
  rw [hargs]
  exact ⟨parseGas, outF, hprovider, hbudget⟩

end WNear.Binary.BalanceOf297AbsentCall
