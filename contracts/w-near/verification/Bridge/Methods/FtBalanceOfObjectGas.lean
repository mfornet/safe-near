import Bridge.Methods.FtBalanceOfObjectAdequacy
import Bridge.Functions.SerdeObjectParserGas
import Bridge.Methods.FtBalanceOfModelGas

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic WNear.Binary
open SerdeRead ParseStrSuccess ParseStr ParseEscape NearInterface.Json
set_option maxRecDepth 20000 in
theorem object_body_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest)) :
    objectBodyCost p.wasm h0 h S a bs rest N ≤
      100 * 10 ^ 9 + 397500000 * bs.length + initialBodyHostUse h0 h a bs := by
  have hp := SerdeObjectNoEsc.parser_cost_linear p.wasm 1 bs rest a N hnb ho hloop
  simp only [SerdeAcctHyp.x169, Nat.one_mul, Nat.reduceAdd] at hp
  have hi := input_cost_le p.wasm h0 bs hinput hlen
  have hs := suffix_cost_le p.wasm 2 h S a (by decide)
  have hcst := Nat.mul_le_mul_left 106069 hc.regularOp
  have hbase := Nat.mul_le_mul_left 8 hc.linearBase
  have hunit := Nat.mul_le_mul_left 264 hc.linearUnit
  have hlin : 483 * p.wasm.regularOpCost ≤ 397500000 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  have hcombine : 470 * bs.length * p.wasm.regularOpCost + 13 * bs.length * p.wasm.regularOpCost =
      483 * bs.length * p.wasm.regularOpCost := by ring
  simp only [objectBodyCost, initialBodyHostUse]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hp hi hlinear hcombine ⊢
  omega

theorem object_host_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h : NearState) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (hext : h.extCosts = p.wasm.extCosts) (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hnone : h.storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    initialBodyHostUse h (NearLogic.inputHost h 0) a bs ≤
      200 * 10 ^ 9 + (3 * 10 ^ 6) * bs.length +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey) * NearLogic.trieNodeMax h +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) * NearLogic.trieNodeMax h +
      NearLogic.valueReturnDataGas h 3 := by
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
  rw [initial_host_input_eq]
  simp only [NearLogic.inputUse, NearLogic.inputChargeList, NearLogic.registerLenUse, NearLogic.registerLenChargeList,
    NearLogic.readRegisterUse, NearLogic.readRegisterChargeList, NearLogic.storageReadUse, hv', hnone,
    NearLogic.storageReadPhaseUse, StateReadModel.header_length, Option.map_some, Option.getD_some,
    Option.map_none, Option.getD_none, NearLogic.chargesUse, NearLogic.chargeUse,
    NearLogic.storageReadBeforeCharges, storageReadValueCharges, writeReg, NearLogic.valueReturnUse, NearLogic.valueReturnChargeList,
    List.map, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append,
    show ¬ (29 > 4000) by decide, ite_false, Nat.mul_one, Nat.add_zero, hext]
  have := hc.base; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  simp only [Nat.mul_add, Nat.add_mul] at hlin
  omega

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic WNear.Binary
open SerdeRead ParseStrSuccess ParseStr ParseEscape NearInterface.Json
open NearInterface in
set_option maxRecDepth 20000 in
theorem object_total_cost_le_model (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length < 2 ^ 24)
    (hreceipt : bs.length ≤ 4194304)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hnone : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    NearLogic.chargesUse (hostOf ctx raw) (loadingCharges size) + 11 * ctx.protocol.wasm.regularOpCost +
      objectBodyCost ctx.protocol.wasm (NearLogic.erase (hostOf ctx raw))
        (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a bs rest N ≤
      (WNear.wnear cfg).gas ctx st (.ftBalanceOf a) := by
  have hinput : (NearLogic.erase (hostOf ctx raw)).context.input = bs := hargs
  have hext : (NearLogic.erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hb := object_body_cost_le ctx.protocol hc (NearLogic.erase (hostOf ctx raw))
    (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a bs rest N hinput hlen hnb ho hloop
  have hh := object_host_cost_le ctx.protocol hc (NearLogic.erase (hostOf ctx raw)) S a bs hext hv hnone
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
