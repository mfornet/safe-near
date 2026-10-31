import Bridge.Functions.SerdeBundledProvider
import Bridge.Functions.SerdePrefixSelectedValues

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.SerdeObjectMixedTrace
open NearInterface ContractModel in
theorem fully_bundled_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm (selectedBundledKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) bs rest N) 44)
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
  exact bundled_refines_init cfg size codeOf raw ctx S a bs rest N
    (selectedBundledKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1)
    (selectedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) hlen hp hwf hm hl
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_bundled_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    (fun len _ => Bound.selected_value_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1)
    (fun len _ => Bound.selected_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    ho hloop hend hbudget hargs hrep ha

end WNear.Binary.SerdeObjectPrefix
