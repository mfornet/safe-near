import Bridge.Functions.SerdeObjectLedgerRoom
import Bridge.Functions.SerdeObjectLedgerProvider

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.SerdeStructModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
theorem ledger_gas_parser_family (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (bs rest : List UInt8) (a : WNear.AccountId) (N F : Nat) (K646 K169 K81 : Nat → Nat)
    (hlen : bs.length ≤ 4194304) (hF : 1 ≤ F)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges cfg bs (Ledger bs len F false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges cfg bs (Ledger bs len F true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges cfg bs (Ledger bs len F false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg bs K81 (Ledger bs len F false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg bs K81 (Ledger bs len F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.ParserFamily (GF := GF) cfg lim inst mi A n g ta gt bs a F
      (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43) (ledgerParserCode n inst mi A) := by
  apply ledger_parser_family cfg lim inst mi A n g ta hm gt bs rest a N F K646 K169 K81 hlen hF
  · intro len hL
    exact Ledger.key_charges cfg bs len F false K646 hlen (input_ledger_bounds bs len F hlen hF hL).1 (hkeys len hL)
  · intro len hL
    exact Ledger.key_charges cfg bs len F true K646 hlen (input_ledger_bounds bs len F hlen hF hL).1 (hkeysSaved len hL)
  · intro len hL
    exact Ledger.value_charges cfg bs len F K169 hlen (input_ledger_bounds bs len F hlen hF hL).1 (hvalues len hL)
  · exact hignored
  · exact hignoredSaved
  · exact ho
  · exact hloop
  · exact hend

end Resource

theorem ledger_gas_deployed_parser_provider (cfg : RuntimeConfig) (bs rest : List UInt8) (a : WNear.AccountId)
    (N : Nat) (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges cfg.wasm bs (Ledger bs len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges cfg.wasm bs (Ledger bs len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges cfg.wasm bs (Ledger bs len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg.wasm bs K81 (Ledger bs len 1 false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg.wasm bs K81 (Ledger bs len 1 true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297AbsentCall.DeployedParserProvider cfg bs a (ledgerParserCost cfg.wasm K646 K169 K81 bs rest N) 44 := by
  intro h _
  apply BalanceOf297AbsentCall.parser_family_mono cfg.wasm execLimits 0 wInst id 0 0 0
    InitialState.g0.type bs a 1 (ledgerParserCost cfg.wasm K646 K169 K81 bs rest N) 44
    (FromSliceSpec.codeCtx cfg h) (ledgerParserCode 0 0 wInst id) (ledger_parser_code_of_context cfg h)
  exact ledger_gas_parser_family cfg.wasm execLimits 0 wInst id 0 0 0 Interface.wInst_ifaceMod InitialState.g0.type
    bs rest a N 1 K646 K169 K81 hlen (by decide) hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend

open NearInterface ContractModel in
/-- The original model-budget witness is coupled to this actual general-object parser. -/
theorem ledger_gas_provider_plan (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw modelSt ctx S a
      (ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N) 44) :
    BalanceOf297AbsentCall.AbsentParserPlan cfg size raw modelSt ctx S a bs := by
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact ⟨ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N, 44, by omega, hpos,
    ledger_gas_deployed_parser_provider ctx.protocol bs rest a N K646 K169 K81 hlen
      hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend, hbudget⟩

open NearInterface ContractModel in
theorem ledger_gas_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (K646 K169 K81 : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyGasCharges ctx.protocol.wasm bs (Ledger bs len 1 true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueGasCharges ctx.protocol.wasm bs (Ledger bs len 1 false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges ctx.protocol.wasm bs K81 (Ledger bs len 1 true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm K646 K169 K81 bs rest N) 44)
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
  have hPlan := ledger_gas_provider_plan cfg ctx raw (some S) S a bs rest N size K646 K169 K81 hlen
    hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hend hbudget
  exact BalanceOf297AbsentCall.provider_plan_refines_init cfg size codeOf raw ctx S a bs
    hp hwf hm hl hPlan hargs hrep ha


end WNear.Binary.SerdeObjectMixedTrace
