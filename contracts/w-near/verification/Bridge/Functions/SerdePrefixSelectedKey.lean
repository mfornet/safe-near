import Bridge.Functions.SerdePrefixTrace
import Bridge.Functions.SerdePrefixProvider

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near
open WNear.Binary.ScratchMixedTrace

theorem Bound.selected_key_charges (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) : KeyGasCharges cfg bs (Bound bs start baseHL baseF saved)
      (selectedKeyCost cfg bs start baseF) := by
  intro first i q key rest hl F cap hi hq hs hb hc hal hp
  obtain ⟨pre, hprefix, hcap, hfree, hlo, hhi⟩ := hb
  subst cap F
  exact Nat.le_of_eq (selectedKeyCost_of_witness cfg bs start baseF q
    ⟨first, i, key, rest, pre, saved, hprefix, hq, hs⟩)

end WNear.Binary.SerdeObjectPrefix


namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.SerdeObjectMixedTrace
open NearInterface ContractModel in
theorem selected_key_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 false) K81)
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreGasCharges ctx.protocol.wasm bs (Bound bs (wsLen bs + 1) len 1 true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm (selectedKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1) K169 K81 bs rest N) 44)
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
  exact prefix_refines_init cfg size codeOf raw ctx S a bs rest N (selectedKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1) K169 K81 hlen hp hwf hm hl
    (fun len _ => Bound.selected_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_key_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    hvalues hignored hignoredSaved ho hloop hend hbudget hargs hrep ha

end WNear.Binary.SerdeObjectPrefix
