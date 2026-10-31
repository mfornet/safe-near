import Bridge.Methods.FtBalanceOfPresentRefines

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.U128From (u128Bytes)
theorem present_host_input_eq (h : NearState) (a : WNear.AccountId) (bs : List UInt8) (lo hi : UInt64) :
    presentBodyHostUse h (NearLogic.inputHost h 0) a bs lo hi =
    NearLogic.inputUse h + NearLogic.registerLenUse h + NearLogic.readRegisterUse h bs.length +
    NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
    NearLogic.storageReadUse h (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
    NearLogic.registerLenUse h + NearLogic.readRegisterUse h 16 +
    NearLogic.valueReturnUse h (resultLen lo hi).toNat := rfl

set_option maxRecDepth 20000 in
theorem present_host_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h : NearState) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8)
    (hext : h.extCosts = p.wasm.extCosts) (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hsome : h.storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi)) :
    presentBodyHostUse h (NearLogic.inputHost h 0) a bs lo hi ≤
      300 * 10 ^ 9 + (3 * 10 ^ 6) * bs.length +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey) * NearLogic.trieNodeMax h +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) * NearLogic.trieNodeMax h +
      NearLogic.valueReturnDataGas h (resultLen lo hi).toNat := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hn : a.val.utf8ByteSize ≤ 64 := by
    rw [← Wasm.ByteEncoding.string_utf8_length]; exact hvalid.1.2
  have hk : 5 + a.val.utf8ByteSize ≤ 69 := by omega
  have hkm := Nat.mul_le_mul hc.readMemoryByte hk
  have hks := Nat.mul_le_mul hc.storageReadKeyByte hk
  have hcoef : p.wasm.extCosts.cost "read_register_byte" + p.wasm.extCosts.cost "write_memory_byte" ≤ 3 * 10 ^ 6 := by
    have := hc.readRegisterByte; have := hc.writeMemoryByte; omega
  have hlin := Nat.mul_le_mul_right bs.length hcoef
  have hv' : h.storage StateRead.stateKey = some (WNear.header S) := by simpa only [StateRead.stateKey_eq] using hv
  have hret : (resultLen lo hi).toNat ≤ 41 := by
    rw [resultLen_toNat]; have := FmtString.decDigits_le lo hi; omega
  have hretmem := Nat.mul_le_mul hc.readMemoryByte hret
  rw [present_host_input_eq]
  simp only [NearLogic.inputUse, NearLogic.inputChargeList, NearLogic.registerLenUse, NearLogic.registerLenChargeList,
    NearLogic.readRegisterUse, NearLogic.readRegisterChargeList, NearLogic.storageReadUse, hv', hsome,
    NearLogic.storageReadPhaseUse, StateReadModel.header_length, U128From.u128Bytes_length, Option.map_some, Option.getD_some,
    NearLogic.chargesUse, NearLogic.chargeUse,
    NearLogic.storageReadBeforeCharges, storageReadValueCharges, writeReg, NearLogic.valueReturnUse, NearLogic.valueReturnChargeList,
    List.map, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append,
    show ¬ (29 > 4000) by decide, show ¬ (16 > 4000) by decide, ite_false, Nat.mul_one, Nat.add_zero, hext]
  have := hc.base; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  simp only [Nat.add_mul] at hlin hretmem
  omega


end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall (initial_body_trie_le)
open WNear.Binary.U128From (u128Bytes)
open NearInterface ContractModel in
theorem present_model_budget_of_parser_linear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8) (parseGas outF size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304) (hF : outF ≤ 44)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * ctx.protocol.wasm.regularOpCost)
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hsome : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi)) :
    PresentProviderModelBudget cfg size raw st ctx S a lo hi parseGas outF := by
  have hinput : (NearLogic.erase (hostOf ctx raw)).context.input = bs := hargs
  have hext : (NearLogic.erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hsmall : bs.length < 2 ^ 24 := by omega
  have hb := present_provider_body_linear_cost ctx.protocol hc (NearLogic.erase (hostOf ctx raw))
    (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a lo hi bs parseGas outF hinput hsmall hF hparse
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

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem present_parser_family_mono (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (gt : GlobalType) (bs : List UInt8) (a : WNear.AccountId)
    (F parseGas outF : Nat) (Cd Ce : IProp GF) (hCode : Cd ⊢ Ce)
    (hp : PresentParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Ce) :
    PresentParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd := by
  intro Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL
  exact hCode.trans (hp Cg d sp out ptr idx ob len live hd hob hout hlen hptr hsp hal hL)


end WNear.Binary.BalanceOf297PresentCall
