import Bridge.Methods.FtBalanceOfObjectRefines
import Bridge.Exported

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open NearInterface NearInterface.ContractModel
open SerdeRead ParseStr

/-- Initialized, absent account and escape-free object input with shallow ignored values, within 4 MiB.
This is the exact completed input/state case, not an additional proof obligation. -/
def ObjectAbsentCase (st : Option WNear.State) (ctx : Context) (c : WNear.Call) : Prop :=
  ∃ (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat),
    st = some S ∧ c = .ftBalanceOf a ∧ a ∉ S.registered ∧ ctx.args = bs ∧
    bs.length ≤ 4194304 ∧ (0x5C : UInt8) ∉ bs ∧ bs[wsLen bs]? = some 0x7B ∧
    WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest) ∧
    bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length

theorem object_case_accepted (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : ObjectAbsentCase st ctx c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st c
    ((WNear.wnear cfg).gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st c) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st c) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, hnb, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (object_absent_refines_init cfg size codeOf raw ctx S a bs rest N hp hwf hm hc hl
    hsize hlen hreceipt hnb ho hloop hend hargs hrep ha).2

theorem object_case_no_issue (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (he : Exported.Environment protocol) (hsize : size ≤ 185625)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (c : WNear.Call)
    (hrep : (WNear.wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hctx : ctx.protocol = protocol) (hm : ctx.method = "ft_balance_of")
    (hcase : ObjectAbsentCase st ctx c) :
    ∀ msg, (Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx).outcome ≠
      .error (.executionIssue msg) := by
  obtain ⟨S, a, bs, rest, N, rfl, rfl, ha, hargs, hreceipt, hnb, ho, hloop, hend⟩ := hcase
  have hlen : bs.length < 2 ^ 24 := by omega
  have hp : WProtocol ctx.protocol := hctx ▸ he.runtime
  have hc : FtTotalSupplyMethod.CostsV86 ctx.protocol := hctx ▸ he.costs
  have hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol := hctx ▸ he.limits
  exact (object_absent_refines_init cfg size codeOf raw ctx S a bs rest N hp hwf hm hc hl
    hsize hlen hreceipt hnb ho hloop hend hargs hrep ha).1

end WNear.Binary.BalanceOf297AbsentCall
