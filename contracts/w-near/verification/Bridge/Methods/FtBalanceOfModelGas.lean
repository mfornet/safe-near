import Bridge.Methods.FtBalanceOfBodyGas

/-! The model allowance pays loading, activation and the exact initialized body.
This cost inequality does not itself establish accepted-call refinement. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic WNear.Binary
open SerdeRead ParseStrSuccess ParseStr ParseEscape NearInterface.Json

open NearInterface in
set_option maxRecDepth 20000 in
theorem initial_total_cost_le_model (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hnone : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    NearLogic.chargesUse (hostOf ctx raw) (loadingCharges size) + 11 * ctx.protocol.wasm.regularOpCost +
      initialBodyCost ctx.protocol.wasm (NearLogic.erase (hostOf ctx raw))
        (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a bs rest j k ≤
      (WNear.wnear cfg).gas ctx st (.ftBalanceOf a) := by
  have hinput : (NearLogic.erase (hostOf ctx raw)).context.input = bs := hargs
  have hext : (NearLogic.erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hb := initial_body_cost_le ctx.protocol hc (NearLogic.erase (hostOf ctx raw))
    (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a bs rest j k hinput hlen hj hq hk hend hmodel
  have hh := initial_host_cost_le ctx.protocol hc (NearLogic.erase (hostOf ctx raw)) S a bs hext hv hnone
  have ht := initial_body_trie_le ctx raw a
  have hd := FtTotalSupplyMethod.dataGas_le ctx raw 3 (by decide)
  have hgas : (WNear.wnear cfg).gas ctx st (.ftBalanceOf a) =
      WNear.computeGas + WNear.argumentByteGas * bs.length + WNear.trieGas ctx + returnDataGas ctx 41 := by
    change WNear.gasBound ctx (.ftBalanceOf a) = _
    simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
      WNear.Call.resultBytes, WNear.Call.returnBytes, FtTotalSupplyMethod.retBytes, hargs]
    simp
  have hl : NearLogic.chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [NearLogic.chargesUse, loadingCharges, NearLogic.chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  have hact := Nat.mul_le_mul_left 11 hc.regularOp
  have hbase := hc.loadingBase
  rw [hgas, hl]
  simp only [WNear.computeGas, WNear.argumentByteGas, Nat.mul_one]
  omega

end WNear.Binary.BalanceOf297AbsentCall
