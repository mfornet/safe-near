import Bridge.Methods.FtBalanceOfNoneRun
import Bridge.Methods.FtTotalSupplyUninitRefines
import Bridge.Methods.FtBalanceOfPresentBudget

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall (input_cost_le)
def noneBodyHostUse (h : NearState) (bs : List UInt8) : Nat :=
  inputUse h + registerLenUse h + readRegisterUse h bs.length + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31

set_option maxRecDepth 20000 in
theorem none_provider_body_linear_cost (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h : NearState) (bs : List UInt8) (parseGas : Nat)
    (hinput : h.context.input = bs) (hlen : bs.length < 2 ^ 24)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * p.wasm.regularOpCost) :
    noneProviderBodyCost p.wasm h (inputHost h 0) parseGas ≤
      1300 * 10 ^ 9 + 397500000 * bs.length + noneBodyHostUse h bs := by
  have hreg : registerLenUse (inputHost h 0) = registerLenUse h := rfl
  have hread : readRegisterUse (inputHost h 0) bs.length = readRegisterUse h bs.length := rfl
  have hstate : storageReadUse (inputHost h 0) StateRead.stateKey 5 = storageReadUse h StateRead.stateKey 5 := rfl
  have hpanic : panicUtf8Use (inputHost h 0) 31 = panicUtf8Use h 31 := rfl
  have hi := input_cost_le p.wasm h bs hinput hlen
  have hcst := Nat.mul_le_mul_left 10000 hc.regularOp
  have hbase := hc.linearBase
  have hunit := Nat.mul_le_mul_left 257 hc.linearUnit
  have hlin : 483 * p.wasm.regularOpCost ≤ 397500000 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  have hcombine : 470 * bs.length * p.wasm.regularOpCost + 13 * bs.length * p.wasm.regularOpCost =
      483 * bs.length * p.wasm.regularOpCost := by ring
  simp only [noneProviderBodyCost, noneBodyHostUse, hstate, hpanic]
  rw [hreg, hread] at hi
  simp only [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm] at hparse hi hlinear hcombine ⊢
  omega

set_option maxRecDepth 20000 in
theorem none_host_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h : NearState) (bs : List UInt8) (hext : h.extCosts = p.wasm.extCosts)
    (hv : h.storage StateRead.stateKey = none) :
    noneBodyHostUse h bs ≤ 300 * 10 ^ 9 + (3 * 10 ^ 6) * bs.length +
      readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey) * trieNodeMax h := by
  have hcoef : p.wasm.extCosts.cost "read_register_byte" + p.wasm.extCosts.cost "write_memory_byte" ≤ 3 * 10 ^ 6 := by
    have := hc.readRegisterByte; have := hc.writeMemoryByte; omega
  have hlin := Nat.mul_le_mul_right bs.length hcoef
  simp only [noneBodyHostUse, inputUse, inputChargeList, registerLenUse, registerLenChargeList,
    readRegisterUse, readRegisterChargeList, storageReadUse, storageReadPhaseUse, hv, Option.map_none, Option.getD_none,
    panicUtf8Use, panicUtf8Charges, chargesUse, chargeUse, storageReadBeforeCharges,
    List.map, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append, Nat.mul_one, Nat.add_zero, hext]
  have := hc.base; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.storageReadBase; have := hc.storageReadKeyByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  simp only [Nat.add_mul] at hlin
  omega

open NearInterface ContractModel in
set_option maxRecDepth 20000 in
theorem none_model_budget_of_parser_linear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (modelSt : Option WNear.State) (a : WNear.AccountId) (bs : List UInt8) (parseGas size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * ctx.protocol.wasm.regularOpCost)
    (hv : (hostOf ctx raw).storage StateRead.stateKey = none) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + noneProviderMethodCost ctx.protocol parseGas (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) := by
  have hb := none_provider_body_linear_cost ctx.protocol hc (erase (hostOf ctx raw)) bs parseGas hargs (by omega) hparse
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
