import Bridge.Methods.FtBalanceOfObjectGas
import Bridge.Methods.FtBalanceOfProviderRefines
import Bridge.Functions.SerdeBundledSelected

set_option maxRecDepth 20000
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic WNear.Binary
open SerdeRead ParseStrSuccess ParseStr ParseEscape NearInterface.Json

theorem alloc_walk64_cost_le (cfg : WasmConfig) (F P : Nat) (size : UInt32)
    (hF : F ≤ 64) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat ≤ P) :
    AllocWalk.cost310W cfg F size 1 ≤ 21450 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * P := by
  have hf := Nat.mul_le_mul_right (320 * cfg.regularOpCost) hF
  have hpg := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
  simp only [AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc]
  omega

theorem alloc64_cost_le (cfg : WasmConfig) (F P : Nat) (size : UInt32)
    (hF : F ≤ 64) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat ≤ P) :
    VecWithCap.costAllocF cfg F size ≤ 21450 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * P := by
  unfold VecWithCap.costAllocF
  split
  · simp only [VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581]
    have hpg := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
    omega
  · exact alloc_walk64_cost_le cfg F P size hF hp

theorem alloc64_delta (cfg : WasmConfig) (F : Nat) (size : UInt32) (hF : F ≤ 64) :
    VecWithCap.costAllocF cfg F size ≤ VecFromElem.costAlloc cfg false size + 20510 * cfg.regularOpCost := by
  unfold VecWithCap.costAllocF
  split
  · omega
  · have hf := Nat.mul_le_mul_right (320 * cfg.regularOpCost) hF
    simp only [AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc,
      VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581]
    omega

theorem allocW64_delta (cfg : WasmConfig) (F : Nat) (size : UInt32) (hF : F ≤ 64) :
    AllocZeroedF.costAllocW cfg F size ≤ VecFromElem.costAlloc cfg false size + 20510 * cfg.regularOpCost := by
  unfold AllocZeroedF.costAllocW
  split
  · omega
  · have hf := Nat.mul_le_mul_right (320 * cfg.regularOpCost) hF
    simp only [AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc,
      VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581]
    omega

theorem vec_zero64_delta (cfg : WasmConfig) (F : Nat) (size : UInt32) (hF : F ≤ 64) :
    VecFromElemF.cost687Z cfg F size ≤ VecFromElem.cost687 cfg 0 size + 20510 * cfg.regularOpCost := by
  have ha := allocW64_delta cfg F size hF
  rw [VecFromElemF.cost687Z, AllocZeroedF.costZeroF_eq]
  simp only [VecFromElem.cost687, FtTotalSupplyMethod.and0, ite_true, VecFromElem.costAlloc,
    ite_true, Bool.false_eq_true, ite_false, AllocZeroed.cost153] at ha ⊢
  omega

theorem return64_cost_le (cfg : WasmConfig) (F : Nat) (lo hi : UInt64) (hF : F ≤ 64) :
    ToVec.cost96F cfg F lo hi ≤ 60000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) := by
  have ho := FtTotalSupplyMethod.c96 cfg lo hi
  have h1 := alloc64_delta cfg F 128 hF
  have h2 := alloc64_delta cfg F (FmtGrow.newCap 0 (FmtString.kOf (FmtU128.val lo hi))) hF
  simp only [ToVec.cost96, ToVec.cost96F, ToString.cost385, FmtString.cost746, FmtString.cost872,
    FmtString.cost353, FmtString.costGrow,
    VecWithCap.costAllocF_le2 cfg (show 1 ≤ 2 by decide)] at ho ⊢
  omega

theorem read_register64_delta (cfg : WasmConfig) (F : Nat) (h : NearState) (r : UInt64) (hF : F ≤ 64) :
    ReadRegisterF.cost523F cfg F h r ≤ ReadRegister.cost523 cfg h r + 20510 * cfg.regularOpCost := by
  cases hr : h.registers r.toNat with
  | none => simp only [ReadRegisterF.cost523F, ReadRegister.cost523, hr, ReadRegisterF.costRestF, ReadRegister.costRest]; omega
  | some val =>
    have hz := vec_zero64_delta cfg F (UInt32.ofNat val.length) hF
    simp only [ReadRegisterF.cost523F, ReadRegister.cost523, hr, ReadRegisterF.costRestF, ReadRegister.costRest]
    omega

theorem storage_register64_delta (cfg : WasmConfig) (F : Nat) (h : NearState) (v : List UInt8) (hF : F ≤ 64) :
    StorageReadWrapF.costSF cfg F h v ≤ StorageReadWrap.costS cfg h (some v) + 20510 * cfg.regularOpCost := by
  have hr := read_register64_delta cfg F (h.setRegister 0 v) 0 hF
  have he : ReadRegister.cost523 cfg (h.setRegister 0 v) 0 =
      281 * cfg.regularOpCost + NearLogic.registerLenUse h + ReadRegister.costRest cfg h (some v) := rfl
  rw [he] at hr
  simp only [StorageReadWrapF.costSF, StorageReadWrap.costS]
  omega

theorem borsh_contract64_delta (cfg : WasmConfig) (F : Nat) (L : UInt32) (hF : F ≤ 64) :
    BorshContractF.cost161 cfg F L ≤ BorshContract.cost161 cfg L + 20510 * cfg.regularOpCost := by
  have ha := alloc64_delta cfg F L hF
  simp only [BorshContractF.cost161, BorshContract.cost161, BorshFTF.cost425, BorshFT.cost425,
    BorshVecF.cost374, BorshVec.cost374]
  omega

theorem state_read64_delta (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (hF : F ≤ 64) :
    cost219F cfg F h S ≤ FtTotalSupply.cost219 cfg h S + 41020 * cfg.regularOpCost := by
  have hs := storage_register64_delta cfg F h (WNear.header S) hF
  have hb := borsh_contract64_delta cfg F 1 hF
  simp only [cost219F, FtTotalSupply.cost219]
  omega

theorem state_read64_cost_le (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (hF : F ≤ 64) :
    cost219F cfg F h S ≤ 60000 * cfg.regularOpCost +
      2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) + NearLogic.storageReadUse h StateRead.stateKey 5 +
      NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 := by
  have hf := state_read64_delta cfg F h S hF
  have hb := FtTotalSupplyMethod.c161 cfg
  have hv := FtTotalSupplyMethod.c687 cfg
  simp only [FtTotalSupply.cost219, StorageReadWrap.costS, ReadRegister.costRest, StateReadModel.header_length] at hf
  omega

theorem lookup_none64_cost_le (cfg : WasmConfig) (F : Nat) (L : UInt32) (h : NearState) (key : List UInt8)
    (hF : F ≤ 64) (hL : L.toNat ≤ 64) :
    LookupMapGet.cost399None cfg F 1 L h key ≤
      60000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      NearLogic.storageReadUse h key (5 + L.toNat) := by
  have h4 : (0 + 4 + L : UInt32).toNat = 4 + L.toNat := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    omega
  have h5 : (1 + (0 + 4 + L) : UInt32).toNat = 5 + L.toNat := by
    simp only [UInt32.toNat_add, h4, UInt32.reduceToNat]
    omega
  have hp := LookupMapOps.cellPages_le4096 (1 + (0 + 4 + L)) (by rw [h5]; omega)
  have ha := alloc64_cost_le cfg F 1 1024 hF (by decide)
  have hb := alloc64_cost_le cfg F 1 (1 + (0 + 4 + L)) hF (by omega)
  have hc4 : MemCpy.cost 4 ≤ 78 := FtTotalSupplyMethod.memcpy_le 4
  have hcL : MemCpy.cost L.toNat ≤ 1158 := by have := FtTotalSupplyMethod.memcpy_le L.toNat; omega
  have hc1 : MemCpy.cost 1 ≤ 24 := by decide
  have hc4L : MemCpy.cost (0 + 4 + L : UInt32).toNat ≤ 1230 := by
    rw [h4]
    have := FtTotalSupplyMethod.memcpy_le (4 + L.toNat)
    omega
  have h4c := Nat.mul_le_mul_right cfg.regularOpCost hc4
  have hLc := Nat.mul_le_mul_right cfg.regularOpCost hcL
  have h1c := Nat.mul_le_mul_right cfg.regularOpCost hc1
  have h4Lc := Nat.mul_le_mul_right cfg.regularOpCost hc4L
  simp only [LookupMapGet.cost399None, LookupMapBorsh.cost395, LookupMapBorsh.cost377,
    LookupMapLeaves.cost510, h5, UInt32.reduceToNat, Nat.add_mul]
  omega

theorem suffix64_cost_le (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (a : WNear.AccountId)
    (hF : F ≤ 44) : parserSuccessCost cfg F h S a 0 ≤
      200000 * cfg.regularOpCost + 6 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
      NearLogic.storageReadUse h (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
      NearLogic.valueReturnUse h 3 := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hn : a.val.utf8ByteSize ≤ 64 := by
    rw [← Wasm.ByteEncoding.string_utf8_length]; exact hvalid.1.2
  have hsize : (UInt32.ofNat a.val.utf8ByteSize).toNat = a.val.utf8ByteSize := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hs := state_read64_cost_le cfg (F + 1) h S (by omega)
  have hl := lookup_none64_cost_le cfg (F + 2) (UInt32.ofNat a.val.utf8ByteSize) h
    (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (by omega) (by omega)
  have hr := return64_cost_le cfg (F + 5) 0 0 (by omega)
  rw [hsize] at hl
  simp only [parserSuccessCost, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  omega


theorem provider_body_linear_cost (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF : Nat)
    (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24) (hF : outF ≤ 44)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * p.wasm.regularOpCost) :
    providerBodyCost p.wasm h0 h S a parseGas outF ≤
      1200 * 10 ^ 9 + 397500000 * bs.length + initialBodyHostUse h0 h a bs := by
  have hi := input_cost_le p.wasm h0 bs hinput hlen
  have hs := suffix64_cost_le p.wasm outF h S a hF
  have hcst := Nat.mul_le_mul_left 220000 hc.regularOp
  have hbase := Nat.mul_le_mul_left 8 hc.linearBase
  have hunit := Nat.mul_le_mul_left 264 hc.linearUnit
  have hlin : 483 * p.wasm.regularOpCost ≤ 397500000 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  have hcombine : 470 * bs.length * p.wasm.regularOpCost + 13 * bs.length * p.wasm.regularOpCost =
      483 * bs.length * p.wasm.regularOpCost := by ring
  simp only [providerBodyCost, initialBodyHostUse]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hparse hi hlinear hcombine ⊢
  omega

open NearInterface ContractModel in
theorem provider_model_budget_of_parser_linear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage)
    (st : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF size : Nat)
    (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hargs : ctx.args = bs) (hlen : bs.length ≤ 4194304) (hF : outF ≤ 44)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * ctx.protocol.wasm.regularOpCost)
    (hv : (NearLogic.erase (hostOf ctx raw)).storage WNear.stateKey = some (WNear.header S))
    (hnone : (NearLogic.erase (hostOf ctx raw)).storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    ProviderModelBudget cfg size raw st ctx S a parseGas outF := by
  have hinput : (NearLogic.erase (hostOf ctx raw)).context.input = bs := hargs
  have hext : (NearLogic.erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hsmall : bs.length < 2 ^ 24 := by omega
  have hb := provider_body_linear_cost ctx.protocol hc (NearLogic.erase (hostOf ctx raw))
    (NearLogic.inputHost (NearLogic.erase (hostOf ctx raw)) 0) S a bs parseGas outF hinput hsmall hF hparse
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
  unfold ProviderModelBudget providerMethodCost
  rw [hgas, hl]
  simp only [WNear.computeGas, WNear.argumentByteGas, Nat.mul_one]
  omega

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WasmLogic WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open SerdeObjectMixedTrace

/-- Exact remaining selected-parser inequality; excludes host/suffix/loading costs already composed below. -/
noncomputable def SelectedParserLinearBudget (cfg : WasmConfig) (bs rest : List UInt8) (N : Nat) : Prop :=
  ledgerParserCost cfg (selectedBundledKeyCost cfg bs (wsLen bs + 1) 1)
    (selectedValueCost cfg bs (wsLen bs + 1) 1) (selectedIgnoreCost cfg bs (wsLen bs + 1) 1) bs rest N ≤
    1000000000000 + (2215 + 470 * bs.length) * cfg.regularOpCost

open NearInterface ContractModel in
set_option maxHeartbeats 4000000 in
theorem linear_bundled_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hcosts : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hparse : SelectedParserLinearBudget ctx.protocol.wasm bs rest N)
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
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  have hkey := NearDepositMethod.accountKey_ofNear a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hkey
  change WNear.accountKey a = WNear.accountsPrefix ++
    (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList) at hkey
  rw [Wasm.ByteEncoding.string_utf8_length] at hkey
  have hnone : (hostOf ctx raw).storage (BalanceOf297AbsentCall.copiedKey a) = none := by
    have hr := FtBalanceOfMethod.reg_storage ctx raw S hwf hraw (hostOf ctx raw) rfl a
    rw [hkey] at hr
    simpa only [NearDepositMethod.regOf, if_neg ha, Option.map_none] using hr
  have hbudget := BalanceOf297AbsentCall.provider_model_budget_of_parser_linear cfg ctx raw (some S) S a bs
    _ 44 size hcosts hsize hargs hlen (by decide) hparse hval hnone
  exact fully_bundled_refines_init cfg size codeOf raw ctx S a bs rest N hlen hp hwf hm hl ho hloop hend hbudget hargs hrep ha

end WNear.Binary.SerdeObjectPrefix
