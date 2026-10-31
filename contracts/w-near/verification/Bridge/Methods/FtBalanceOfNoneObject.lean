import Bridge.Methods.FtBalanceOfNoneRefines

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic NearInterface WNear.Binary
open WNear.Binary.SerdeObjectMixedTrace WNear.Binary.SerdeObjectPrefix
open ContractModel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem full_object_none_refines (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (ctx : Context) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304)
    (ho : bs[SerdeRead.wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      SerdeIgnObject.ignored N none (bs.drop (SerdeRead.wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + SerdeRead.wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨ (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hparse := selected_weighted_parser_linear_full ctx.protocol.wasm bs rest N a hlen ho hloop
    hc.regularOp hc.linearBase hc.linearUnit
  have hProvider := bundled_deployed_parser_provider_weighted ctx.protocol bs rest a N
    (selectedBundledKeyCost ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) 1)
    (selectedValueCost ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) 1)
    (selectedWeightedIgnoreCost ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) 1) hlen
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) len 1 true)
    (fun len _ => Bound.selected_value_charges ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) len 1)
    (fun len _ => Bound.selected_weighted_ignore_charges ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_weighted_ignore_charges ctx.protocol.wasm bs (SerdeRead.wsLen bs + 1) len 1 true)
    ho hloop hend
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact provider_none_refines cfg size codeOf raw ctx a bs _ 44 hp hwf hrep hm hl hc hsize hargs hlen hpos hProvider hparse
end WNear.Binary.BalanceOf297NoneCall
