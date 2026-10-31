import Bridge.Methods.FtBalanceOfNoneObject
import Bridge.Methods.FtBalanceOfPresentArray

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary NearInterface ContractModel
variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem present_family_for_none (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (gt : GlobalType) (bs : List UInt8) (a : WNear.AccountId)
    (F parseGas outF : Nat) (Cd : IProp GF)
    (hp : BalanceOf297PresentCall.PresentParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
    BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd := by
  intro Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL
  have hs := hp Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL
  unfold BalanceOf297PresentCall.PresentParserCallContract at hs
  unfold BalanceOf297AbsentCall.ParserCallContract
  apply hs.trans
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, Hs, Hvt, Hbs, He, Hw, Hhex, HFr, %hl', %hr, Hparser⟩
  iframe Hg Hs Hvt Hbs He Hw Hhex HFr
  isplitr
  · ipureintro; exact hrs
  iexists hl'
  iframe Hparser
  ipureintro
  exact ParseStrRoom.heap_room_mono hr (by decide)

end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.BalanceOf297PresentCall (presentArrayParserGas)
open WNear.Binary.BalanceOf297AbsentCall (input_cost_le copied_array_parser_cost_le300b)

set_option maxRecDepth 20000 in
theorem none_array_body_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h : NearState) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (hinput : h.context.input = bs) (hlen : bs.length < 2 ^ 24)
    (hj : j = SerdeRead.wsLen bs + 1 + SerdeRead.wsLen (bs.drop (SerdeRead.wsLen bs + 1)))
    (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + SerdeRead.wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + SerdeRead.wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    noneProviderBodyCost p.wasm h (inputHost h 0) (presentArrayParserGas p.wasm bs a rest j k) ≤
      1000 * 10 ^ 9 + 100000000 * bs.length + noneBodyHostUse h bs := by
  have hparse := copied_array_parser_cost_le300b p hc bs a rest j k hlen hj hq hk hend hmodel
  have hi := input_cost_le p.wasm h bs hinput hlen
  have hreg : registerLenUse (inputHost h 0) = registerLenUse h := rfl
  have hread : readRegisterUse (inputHost h 0) bs.length = readRegisterUse h bs.length := rfl
  have hstate : storageReadUse (inputHost h 0) StateRead.stateKey 5 = storageReadUse h StateRead.stateKey 5 := rfl
  have hpanic : panicUtf8Use (inputHost h 0) 31 = panicUtf8Use h 31 := rfl
  rw [hreg, hread] at hi
  have hcst := Nat.mul_le_mul_left 10000 hc.regularOp
  have hbase := hc.linearBase
  have hunit := Nat.mul_le_mul_left 257 hc.linearUnit
  have hlin : 13 * p.wasm.regularOpCost + 80000000 ≤ 100000000 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  simp only [noneProviderBodyCost, noneBodyHostUse, presentArrayParserGas, hstate, hpanic]
  simp only [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm] at hparse hi hlinear ⊢
  omega
open NearInterface ContractModel in
set_option maxRecDepth 20000 in
theorem none_array_model_budget (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304)
    (hj : j = SerdeRead.wsLen bs + 1 + SerdeRead.wsLen (bs.drop (SerdeRead.wsLen bs + 1)))
    (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + SerdeRead.wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + SerdeRead.wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hv : (hostOf ctx raw).storage StateRead.stateKey = none) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + noneProviderMethodCost ctx.protocol (presentArrayParserGas ctx.protocol.wasm bs a rest j k) (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) := by
  have hb := none_array_body_cost_le ctx.protocol hc (erase (hostOf ctx raw)) a bs rest j k hargs (by omega) hj hq hk hend hmodel
  have hh := none_host_cost_le ctx.protocol hc (erase (hostOf ctx raw)) bs rfl hv
  have hrn := readNodes_of_false (h := erase (hostOf ctx raw)) rfl
  rw [hrn] at hh
  have ht := FtTotalSupplyMethod.trie_le ctx raw
  have hgas : (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) =
      WNear.computeGas + WNear.argumentByteGas * bs.length + WNear.trieGas ctx + returnDataGas ctx 41 := by
    change WNear.gasBound ctx (.ftBalanceOf a) = _
    simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
      WNear.Call.resultBytes, WNear.Call.returnBytes, FtTotalSupplyMethod.retBytes, hargs]
    simp
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  have hact := Nat.mul_le_mul_left 11 hc.regularOp
  have hbase := hc.loadingBase
  unfold noneProviderMethodCost
  rw [hgas, hl]
  simp only [WNear.computeGas, WNear.argumentByteGas, Nat.mul_one]
  omega
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary NearInterface ContractModel
open WNear.Binary.SerdeRead (wsLen)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem full_array_none_refines (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
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
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw none) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx none (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hval : (hostOf ctx raw).storage StateRead.stateKey = none := by
    have hraw : raw = ∅ := hrep
    rw [hraw, StateRead.stateKey_eq]
    exact FtTotalSupplyMethod.hostOf_storage_empty ctx _
  have hbudget := none_array_model_budget cfg ctx raw none a bs rest j k size hcosts hsize hargs hlen hj hq hk hend hmodel hval
  have hProvider := BalanceOf297PresentCall.array_present_deployed_provider ctx.protocol bs rest a j k
    ho hj hq he hk hend hmodel
  have hProvider' : NoneDeployedParserProvider ctx.protocol bs a
      (BalanceOf297PresentCall.presentArrayParserGas ctx.protocol.wasm bs a rest j k)
      (BalanceOf297AbsentCall.copiedParserFree bs (j + 1) 1) := by
    intro h _
    exact present_family_for_none _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hProvider h)
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact provider_none_refines_with_budget cfg size codeOf raw ctx a bs _ _ hp hwf hrep hm hl hcosts hsize
    hargs hlen hpos hProvider' hbudget
end WNear.Binary.BalanceOf297NoneCall
