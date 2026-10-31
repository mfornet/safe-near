import Bridge.Functions.SerdePresentArrayProvider

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.BalanceOf297AbsentCall (input_cost_le copiedParserFree copied_parser_free_le12
  copied_array_parser_cost_le300b initial_body_trie_le)

set_option maxRecDepth 20000 in
theorem present_array_body_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64)
    (bs rest : List UInt8) (j k : Nat) (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24)
    (hj : j = SerdeRead.wsLen bs + 1 + SerdeRead.wsLen (bs.drop (SerdeRead.wsLen bs + 1)))
    (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + SerdeRead.wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + SerdeRead.wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    presentProviderBodyCost p.wasm h0 h S a lo hi (presentArrayParserGas p.wasm bs a rest j k)
      (copiedParserFree bs (j + 1) 1) ≤
      1000 * 10 ^ 9 + 100000000 * bs.length + presentBodyHostUse h0 h a bs lo hi := by
  have hparse := copied_array_parser_cost_le300b p hc bs a rest j k hlen hj hq hk hend hmodel
  have hfree := copied_parser_free_le12 bs a (j + 1) rest hmodel hlen
  have hinputCost := input_cost_le p.wasm h0 bs hinput hlen
  have hs := present_suffix64_cost_le p.wasm (copiedParserFree bs (j + 1) 1) h S a lo hi (by omega)
  have hcst := Nat.mul_le_mul_left 260000 hc.regularOp
  have hbase := Nat.mul_le_mul_left 9 hc.linearBase
  have hunit := Nat.mul_le_mul_left 265 hc.linearUnit
  have hlin : 13 * p.wasm.regularOpCost + 80000000 ≤ 100000000 := by
    have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  simp only [presentProviderBodyCost, presentArrayParserGas, presentBodyHostUse]
  simp only [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm] at hparse hinputCost hlinear ⊢
  omega
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.BalanceOf297AbsentCall (copiedParserFree initial_body_trie_le)
open NearInterface ContractModel in
theorem present_array_model_budget (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs rest : List UInt8) (j k size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304)
    (hj : j = SerdeRead.wsLen bs + 1 + SerdeRead.wsLen (bs.drop (SerdeRead.wsLen bs + 1)))
    (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + SerdeRead.wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + SerdeRead.wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hsome : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi)) :
    PresentProviderModelBudget cfg size raw st ctx S a lo hi
      (presentArrayParserGas ctx.protocol.wasm bs a rest j k) (copiedParserFree bs (j + 1) 1) := by
  have hinput : (NearLogic.erase (hostOf ctx raw)).context.input = bs := hargs
  have hext : (NearLogic.erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hsmall : bs.length < 2 ^ 24 := by omega
  have hb := present_array_body_cost_le ctx.protocol hc (NearLogic.erase (hostOf ctx raw))
    (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a lo hi bs rest j k hinput hsmall hj hq hk hend hmodel
  have hh := present_host_cost_le ctx.protocol hc (NearLogic.erase (hostOf ctx raw)) S a lo hi bs hext hv hsome
  have ht := initial_body_trie_le ctx raw a
  have hret : (resultLen lo hi).toNat ≤ 41 := by
    rw [resultLen_toNat]; have := FmtString.decDigits_le lo hi; omega
  have hd := FtTotalSupplyMethod.dataGas_le ctx raw (resultLen lo hi).toNat hret
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
  unfold PresentProviderModelBudget presentProviderMethodCost
  rw [hgas, hl]
  simp only [WNear.computeGas, WNear.argumentByteGas, Nat.mul_one]
  omega



end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open NearInterface ContractModel in
theorem full_array_present_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hcosts : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∈ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  have hkey := NearDepositMethod.accountKey_ofNear a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hkey
  change WNear.accountKey a = WNear.accountsPrefix ++
    (WasmLogic.bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList) at hkey
  rw [Wasm.ByteEncoding.string_utf8_length] at hkey
  let pair := NearDepositMethod.balanceWords (S.balance a)
  have hsome : (hostOf ctx raw).storage (BalanceOf297AbsentCall.copiedKey a) =
      some (U128From.u128Bytes pair.1 pair.2) := by
    have hr := FtBalanceOfMethod.reg_storage ctx raw S hwf hraw (hostOf ctx raw) rfl a
    rw [hkey] at hr
    simpa only [NearDepositMethod.regOf, ha, ite_true, Option.map_some, U128From.u128Bytes] using hr
  have hbudget := BalanceOf297PresentCall.present_array_model_budget cfg ctx raw (some S) S a
    pair.1 pair.2 bs rest j k size hcosts hsize hargs hlen hj hq hk hend hmodel hval hsome
  have hProvider := BalanceOf297PresentCall.array_present_deployed_provider ctx.protocol bs rest a j k
    ho hj hq he hk hend hmodel
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact BalanceOf297PresentCall.provider_present_refines_init cfg size codeOf raw ctx S a pair.1 pair.2 bs _
    (BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1)
    hp hwf hm hl (by omega) hpos hProvider hbudget hargs hrep hsome

end WNear.Binary.SerdeObjectPrefix
