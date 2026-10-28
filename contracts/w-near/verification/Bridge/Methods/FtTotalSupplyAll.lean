import Bridge.Methods.FtTotalSupplyPre
import Bridge.Methods.FtTotalSupplyUninitRefines

/-!
# `ft_total_supply` (296) refines the model

`ftTotalSupply_refines_all`: the clauses of `Refines` for a call to `ft_total_supply`, on any
storage the model represents: an initialized contract (`ftTotalSupply_refines_init`) or none
(`ftTotalSupply_refines_uninit`, the `PanicOnDefault` panic). Left: the code size, `CostsV86`
and `LimitsV86`, discharged with the protocol at the end.
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near NearLogic NearInterface WNear.Binary

/-- **`ft_total_supply` refines the model.** -/
theorem ftTotalSupply_refines_all (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "ft_total_supply") (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .ftTotalSupply
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .ftTotalSupply ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .ftTotalSupply) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  cases st with
  | none => exact ftTotalSupply_refines_uninit cfg size codeOf raw ctx hp hwf hrep hm hc hl hsize
  | some S => exact ftTotalSupply_refines_init cfg size codeOf raw ctx S hp hwf hrep hm hc hl hsize

end WNear.Binary.FtTotalSupplyMethod
