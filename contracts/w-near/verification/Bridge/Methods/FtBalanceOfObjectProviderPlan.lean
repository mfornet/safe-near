import Bridge.Methods.FtBalanceOfProviderRefines
import Bridge.Methods.FtBalanceOfObjectGas

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead
open NearInterface ContractModel in
theorem object_provider_plan (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hv : (erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hnone : (erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    AbsentParserPlan cfg size raw modelSt ctx S a bs := by
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  refine ⟨SerdeObjectNoEsc.parserCost ctx.protocol.wasm 1 bs rest N, 2, hlen, hpos,
    SerdeObjectNoEsc.deployed_parser_provider ctx.protocol bs rest a N hnb ho hloop hend, ?_⟩
  have hbound := object_total_cost_le_model cfg ctx raw modelSt S a bs rest N size hc hsize hargs
    hlen hreceipt hnb ho hloop hv hnone
  simpa only [ProviderModelBudget, providerMethodCost, providerBodyCost, objectBodyCost, Nat.add_assoc] using hbound

end WNear.Binary.BalanceOf297AbsentCall
