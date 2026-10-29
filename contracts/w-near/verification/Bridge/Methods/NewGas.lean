import Bridge.Methods.NewRuns
import Bridge.Methods.NewPanicsRefines

/-!
# `new` (290) on an uninitialized contract: the cost against the model's gas bound

* `costNew290_le`: the success path's cost is at most `60000` Wasm operations, `20` linear ones,
  and the host calls: `attached_deposit`, `storage_has_key(STATE)`, `storage_usage` twice, the
  write and the removal of the dummy record (with `read_register` of the evicted value) and the
  write of `STATE` (`hostUse`).
-/

namespace WNear.Binary.NewGas

open Wasm Wasm.Near NearLogic
open WNear.Binary WNear.Binary.NewBody
open WNear.Binary.MeasureUsage (mKey mVal cost404)
open WNear.Binary.LookupMapOps (cost401 cost402)
open WNear.Binary.VecWithCap (costAllocF)
open WNear.Binary.StorageWrite (evictedRegister)

section Ops

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem pages1 (s : UInt32) (hs : s.toNat ≤ 4096) : (AllocNewCell.cellPages (AllocAlloc.wordsOf s) 1).toNat = 1 :=
  LookupMapOps.cellPages_le4096 s hs

theorem cA1 (s : UInt32) (hs : s.toNat ≤ 4096) : costAllocF cfg 1 s ≤ 940 * c + L := by
  have hp := pages1 s hs
  simp only [costAllocF, show (1 : Nat) ≤ 2 by decide, ite_true, VecFromElem.costAlloc, Bool.false_eq_true,
    ite_false, AllocZeroed.cost581, hp]
  omega

theorem cA4 (s : UInt32) (hs : s.toNat ≤ 4096) : costAllocF cfg 4 s ≤ 2250 * c + L := by
  have hp := pages1 s hs
  simp only [costAllocF, show ¬ (4 : Nat) ≤ 2 by decide, ite_false, AllocWalk.cost310W, AllocWalk.walkCost,
    AllocWalk.wc, hp]
  omega

theorem cA8 (s : UInt32) (hs : s.toNat ≤ 4096) : costAllocF cfg 8 s ≤ 3530 * c + L := by
  have hp := pages1 s hs
  simp only [costAllocF, show ¬ (8 : Nat) ≤ 2 by decide, ite_false, AllocWalk.cost310W, AllocWalk.walkCost,
    AllocWalk.wc, hp]
  omega

theorem cW4 (s : UInt32) (hs : s.toNat ≤ 4096) : AllocZeroedF.costAllocW cfg 4 s ≤ 2250 * c + L := by
  have hp := pages1 s hs
  simp only [AllocZeroedF.costAllocW, show ¬ (4 : Nat) = 1 by decide, ite_false, AllocWalk.cost310W,
    AllocWalk.walkCost, AllocWalk.wc, hp]
  omega

/-- The host calls of the success path. -/
def hostUse (h : NearState) : Nat :=
  attachedDepositUse h + storageHasKeyUse h StateRead.stateKey 5 + 2 * storageUsageUse h +
    storageWriteUse h mKey 69 16 + storageRemoveUse (withDummy h) mKey 69 +
    registerLenUse ((withDummy h).setRegister evictedRegister.toNat mVal) +
    readRegisterUse ((withDummy h).setRegister evictedRegister.toNat mVal) 16 +
    storageWriteUse h StateRead.stateKey 5 29

set_option maxRecDepth 100000 in
/-- **The success path's cost**: Wasm operations and the host calls. -/
theorem costNew290_le (h : NearState) : costNew290 cfg h ≤ 60000 * c + 20 * L + hostUse h := by
  have a1 := cA1 cfg 1 (by decide)
  have a2 := cA1 cfg 64 (by decide)
  have a3 := cA1 cfg 1024 (by decide)
  have a4 := cA1 cfg (1 + (0 + 4 + 64)) (by decide)
  have b1 := cA4 cfg 1024 (by decide)
  have b2 := cA4 cfg (1 + (0 + 4 + 64)) (by decide)
  have b3 := cW4 cfg (UInt32.ofNat 16) (by decide)
  have d1 := cA8 cfg 1024 (by decide)
  have hr : ((withDummy h).setRegister evictedRegister.toNat mVal).registers evictedRegister.toNat = some mVal := by
    simp [NearState.setRegister]
  simp only [costNew290, cost289N, cost220N, cost404, k2New, StrRepeat.cost847_eq, cost401, cost402,
    LookupMapBorsh.cost395, LookupMapBorsh.cost397, LookupMapBorsh.cost377, LookupMapBorsh.cost378,
    LookupMapLeaves.cost510, ReadRegisterF.cost523F, ReadRegisterF.costRestF, hr, VecFromElemF.cost687Z,
    AllocZeroedF.costZeroF_eq, BorshSer.cost48, hostUse, MeasureUsage.mVal_length] at *
  simp only [show (1 + (0 + 4 + 64) : UInt32).toNat = 69 by decide, show (64 : UInt32).toNat = 64 by decide,
    show (1 : UInt32).toNat = 1 by decide, show (0 + 4 + 64 : UInt32).toNat = 68 by decide,
    show (UInt32.ofNat 16).toNat = 16 by decide, show (UInt32.ofNat (List.length mVal)) = UInt32.ofNat 16 by rfl,
    MemCpy.cost, MemSet.cost] at *
  norm_num at *
  omega

end Ops

/-! ## Against the model's bound -/

open NearInterface ContractModel
open WNear.Binary.NewMethod (costNew gas_new loading_eq CostsNewV86)
open WNear.Binary.FtTotalSupplyMethod (CostsV86)

/-- An uninitialized contract stores nothing. -/
theorem hostOf_empty_storage (ctx : Context) (k : List UInt8) : (hostOf ctx ∅).storage k = none := by
  show ((∅ : RawStorage).toList.find? (·.1 == k)).map (·.2) = none
  simp

theorem mKey_length_le : mKey.length ≤ WNear.maxStorageKeyBytes := by
  simp [MeasureUsage.mKey_length, WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes]

set_option maxRecDepth 100000 in
/-- **The model's gas bound covers loading and the success path of `new`**: the trie nodes of
the three mutations within `trieGas` (`trie_writes_le`), the rest within `computeGas`. -/
theorem hbound_new (cfg : WNear.Config) (ctx : Context) (size : Nat) (hc : CostsV86 ctx.protocol)
    (hcn : CostsNewV86 ctx.protocol) (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx ∅) (loadingCharges size) + costNew ctx.protocol (erase (hostOf ctx ∅)) ≤
      (WNear.wnear cfg).gas ctx none .new := by
  have A := costNew290_le ctx.protocol.wasm (erase (hostOf ctx ∅))
  have T := NearDepositGas.trie_writes_le ctx ∅ mKey mKey_length_le StateRead.stateKey rfl
  have hx' : (erase (hostOf ctx ∅)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hid : (erase (hostOf ctx ∅)).context.currentAccountId = ctx.current.bytes := rfl
  have hs : ∀ k, (erase (hostOf ctx ∅)).storage k = none := hostOf_empty_storage ctx
  have hdm : (withDummy (erase (hostOf ctx ∅))).storage mKey = some mVal := by simp [withDummy]
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  generalize hP1 : (2 * (Near.TrieOverlay.contractKey ctx.current.bytes mKey).length + 2) *
    trieNodeMax (erase (hostOf ctx ∅)) = P1
  generalize hP2 : (2 * (Near.TrieOverlay.contractKey ctx.current.bytes StateRead.stateKey).length + 2) *
    trieNodeMax (erase (hostOf ctx ∅)) = P2
  have T' : 2 * P1 + P2 ≤ WNear.trieGas ctx := by
    rw [← hP1, ← hP2, ← Nat.mul_assoc, ← Nat.add_mul]; exact T
  have htm : trieNodeMax (withDummy (erase (hostOf ctx ∅))) = trieNodeMax (erase (hostOf ctx ∅)) := rfl
  have hidD : (withDummy (erase (hostOf ctx ∅))).context.currentAccountId = ctx.current.bytes := rfl
  simp only [hostUse, attachedDepositUse, attachedDepositChargeList, storageHasKeyUse, storageHasKeyBeforeCharges,
    NearDepositGas.readNodes_boundary, Nat.zero_mul, Nat.add_zero, storageUsageUse, storageUsageChargeList,
    storageWriteUse, storageWriteBeforeCharges, storageWritePhaseUse, storageWriteAfter, storageRemoveUse,
    storageRemoveBeforeCharges, storageRemovePhaseUse, storageRemoveAfter, registerLenUse, registerLenChargeList,
    readRegisterUse, readRegisterChargeList, writeReg, hs, hdm, htm, hid, hidD, hP1, hP2, Option.map_none,
    Option.map_some, Option.getD_none, Option.getD_some, MeasureUsage.mVal_length, chargesUse, chargeUse,
    List.map, List.sum_cons, List.sum_nil] at A
  have hxD : (withDummy (erase (hostOf ctx ∅))).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hxR : ((withDummy (erase (hostOf ctx ∅))).setRegister evictedRegister.toNat mVal).extCosts =
    ctx.protocol.wasm.extCosts := rfl
  simp only [hx', hxD, hxR] at A
  refine le_trans ?_ (le_of_eq (gas_new cfg ctx none).symm)
  rw [loading_eq]
  simp only [costNew, WNear.computeGas]
  have := hc.regularOp; have := hc.linearBase; have := hc.linearUnit; have := hc.base
  have := hc.loadingBase; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte
  have := hcn.storageHasKeyBase; have := hcn.storageHasKeyByte; have := hcn.storageWriteBase
  have := hcn.storageWriteKeyByte; have := hcn.storageWriteValueByte; have := hcn.storageRemoveBase
  have := hcn.storageRemoveKeyByte; have := hcn.storageRemoveRetValueByte
  omega

end WNear.Binary.NewGas
