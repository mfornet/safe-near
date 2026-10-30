import Bridge.Methods.FtTotalSupplyGas
import Bridge.Functions.ToVecTwo

/-!
# `ft_total_supply` (296) refines the model, `to_vec` discharged

`ftTotalSupply_refines_v86'`: `ftTotalSupply_refines_v86` with `H96` discharged at `x96 = 0`
(`ToVecTwo.toVecAfterFree_zero`: `to_vec` from the heap `state_read` leaves, `heapInv … 2`, through
`AllocTwo.f310_spec_two`). Left: `hpre` (the host reads `S`: the storage premises of
`storage_read`), the code size, and `CostsV86`.
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary

open NearInterface ContractModel in
/-- **`ft_total_supply` refines the model**, with `to_vec`'s heap premise proved (`x96 = 0`). -/
theorem ftTotalSupply_refines_v86' (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (S : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "ft_total_supply")
    (hpre : ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) → pre S (erase (hostOf ctx raw)))
    (hpreP : pre S (eraseP (hostOf ctx raw)))
    (hc : CostsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .ftTotalSupply
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .ftTotalSupply ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .ftTotalSupply) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) :=
  ftTotalSupply_refines_v86 cfg size codeOf raw st ctx S 0
    (ToVecTwo.toVecAfterFree_zero ctx.protocol.wasm execLimits) hp hwf hrep hm hpre hpreP hc hsize (Nat.zero_le _)

end WNear.Binary.FtTotalSupplyMethod
