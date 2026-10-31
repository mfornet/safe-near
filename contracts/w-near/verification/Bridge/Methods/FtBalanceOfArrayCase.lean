import Bridge.Methods.FtBalanceOfCopiedCase

/-! The initialized absent-account array case, covering borrowed and copied strings. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.ContractModel
open SerdeRead ParseStr

/-- The initialized, unregistered-account, valid-string array branch.
This predicate contains only the input/state case split, not proof obligations. -/
def ArrayAbsentCase (st : Option WNear.State) (ctx : Context) (c : WNear.Call) : Prop :=
  ∃ (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat),
    st = some S ∧ c = .ftBalanceOf a ∧ a ∉ S.registered ∧ ctx.args = bs ∧
    bs.length < 2 ^ 24 ∧ bs[wsLen bs]? = some 0x5B ∧
    j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) ∧ bs[j]? = some 0x22 ∧
    bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D ∧
    k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1 ∧
    k + wsLen (bs.drop k) = bs.length ∧
    Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)

theorem array_case_accepted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : ArrayAbsentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st c
    ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨S, a, bs, rest, j, k, rfl, rfl, ha, hargs, hlen, ho, hj, hq, hendq, hk, hend, hmodel⟩ := hcase
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (array_absent_refines_init cfg size codeOf raw ctx S a bs rest j k hp hwf hm hc hl
    hsize hlen ho hj hq hendq hk hend hmodel hargs hrep ha).2

theorem array_case_no_issue (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : ArrayAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  obtain ⟨S, a, bs, rest, j, k, rfl, rfl, ha, hargs, hlen, ho, hj, hq, hendq, hk, hend, hmodel⟩ := hcase
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (array_absent_refines_init cfg size codeOf raw ctx S a bs rest j k hp hwf hm hc hl
    hsize hlen ho hj hq hendq hk hend hmodel hargs hrep ha).1


/-- The broader completed case contains the previously completed copied-only case. -/
theorem copied_case_is_array_case (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (h : CopiedAbsentCase st ctx c) : ArrayAbsentCase st ctx c := by
  obtain ⟨S, a, bs, rest, j, k, hst, hc, ha, hargs, hlen, ho, hj, hq, he, hk, hend, hmodel, _⟩ := h
  exact ⟨S, a, bs, rest, j, k, hst, hc, ha, hargs, hlen, ho, hj, hq, he, hk, hend, hmodel⟩

end WNear.Binary.BalanceOf297AbsentCall
