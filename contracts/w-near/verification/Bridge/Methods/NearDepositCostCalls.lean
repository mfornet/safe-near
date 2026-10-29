import Bridge.Methods.NearDepositCostOps

/-!
# Bounds for deposit's storage and environment wrappers

Keep each host charge explicit while bounding serialization, allocation and copying
uniformly in the account length and free-list size.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem zero_alloc_le (F : Nat) (hF : F ≤ 32) (s : UInt32) (hs : s.toNat ≤ 64) :
    AllocZeroedF.costZeroF cfg F s ≤ 14000 * c + L := by
  have hp := NewGas.pages1 s (by omega)
  have hw := walk_le cfg F hF
  have hm : MemSet.cost s.toNat ≤ 838 := le_trans (FtTotalSupplyMethod.memset_le _) (by omega)
  have hmGas := Nat.mul_le_mul_right c hm
  rw [AllocZeroedF.costZeroF_eq]
  unfold AllocZeroedF.costAllocW
  split <;> simp only [VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581,
    AllocWalk.cost310W, hp] <;> omega

/-- Reading a present register with at most 64 bytes. -/
theorem read_reg_le (F : Nat) (hF : F ≤ 32) (h : NearState) (r : UInt64) (bs : List UInt8) (hb : bs.length ≤ 64) :
    ReadRegisterF.cost523F cfg F (h.setRegister r.toNat bs) r ≤
      15000 * c + L + registerLenUse h + readRegisterUse h bs.length := by
  have hs : (UInt32.ofNat bs.length).toNat ≤ 64 := by simp; omega
  have hz := zero_alloc_le cfg F hF (UInt32.ofNat bs.length) hs
  have hr : (h.setRegister r.toNat bs).registers r.toNat = some bs := by simp [NearState.setRegister]
  simp only [ReadRegisterF.cost523F, hr, ReadRegisterF.costRestF, VecFromElemF.cost687Z]
  change 281 * c + registerLenUse h + (95 * c + (41 * c + (203 * c +
    AllocZeroedF.costZeroF cfg F (UInt32.ofNat bs.length))) + (237 * c + readRegisterUse h bs.length)) ≤ _
  omega

theorem serialize_account_le (F : Nat) (hF : F ≤ 32) (len : UInt32) (hl : len.toNat ≤ 64) :
    LookupMapBorsh.cost395 cfg F len ≤ 15000 * c + L := by
  have ha := alloc_le cfg F hF 1024 (by decide)
  have hm : MemCpy.cost len.toNat ≤ 1158 := le_trans (FtTotalSupplyMethod.memcpy_le _) (by omega)
  have hmGas := Nat.mul_le_mul_right c hm
  simp only [LookupMapBorsh.cost395, LookupMapBorsh.cost377]
  norm_num [MemCpy.cost, Nat.add_mul] at *
  omega

theorem serialize_balance_le (F : Nat) (hF : F ≤ 32) :
    LookupMapBorsh.cost397 cfg F ≤ 13000 * c + L := by
  have ha := alloc_le cfg F hF 1024 (by decide)
  simp only [LookupMapBorsh.cost397, LookupMapBorsh.cost378]
  norm_num [MemCpy.cost]
  omega

theorem concat_key_le (F : Nat) (hF : F ≤ 32) (len : UInt32) (hl : len.toNat ≤ 64) :
    LookupMapLeaves.cost510 cfg F 1 (0 + 4 + len) ≤ 15000 * c + L := by
  have hl2 : (0 + 4 + len : UInt32).toNat ≤ 68 := by simp; omega
  have hsum : (1 + (0 + 4 + len) : UInt32).toNat ≤ 69 := by simp; omega
  have ha := alloc_le cfg F hF (1 + (0 + 4 + len)) (by omega)
  have hm : MemCpy.cost (0 + 4 + len : UInt32).toNat ≤ 1230 :=
    le_trans (FtTotalSupplyMethod.memcpy_le _) (by omega)
  have hmGas := Nat.mul_le_mul_right c hm
  simp only [LookupMapLeaves.cost510]
  norm_num [MemCpy.cost, Nat.add_mul] at *
  omega

theorem contains_le (F : Nat) (hF : F ≤ 32) (len : UInt32) (hl : len.toNat ≤ 64)
    (h : NearState) (key : List UInt8) :
    LookupMapContains.cost394 cfg F 1 len h key ≤ 32000 * c + 2 * L +
      storageHasKeyUse h key (1 + (0 + 4 + len)).toNat := by
  have hs := serialize_account_le cfg F hF len hl
  have hk := concat_key_le cfg F hF len hl
  simp only [LookupMapContains.cost394, LookupMapContains.cost396]
  omega

theorem get_balance_le (F : Nat) (hF : F ≤ 32) (len : UInt32) (hl : len.toNat ≤ 64)
    (h : NearState) (key bs : List UInt8) (hb : bs.length = 16) :
    InternalDeposit.cost405 cfg F 1 len h key bs ≤ 50000 * c + 3 * L +
      storageReadUse h key (1 + (0 + 4 + len)).toNat + registerLenUse h + readRegisterUse h 16 := by
  have hs := serialize_account_le cfg F hF len hl
  have hk := concat_key_le cfg F hF len hl
  have hr := read_reg_le cfg F hF h 0 bs (by omega)
  rw [hb] at hr
  simp only [UInt64.toNat_zero] at hr
  simp only [InternalDeposit.cost405, LookupMapGet.cost399, StorageReadWrapF.costSF]
  omega

theorem register_le (F : Nat) (hF : F ≤ 32) (len : UInt32) (hl : len.toNat ≤ 64)
    (h : NearState) (key : List UInt8) :
    LookupMapOps.cost401 cfg F 1 len h key ≤ 45000 * c + 3 * L +
      storageWriteUse h key (1 + (0 + 4 + len)).toNat 16 := by
  have hs := serialize_account_le cfg F hF len hl
  have hb := serialize_balance_le cfg F hF
  have hk := concat_key_le cfg F hF len hl
  simp only [LookupMapOps.cost401]
  omega

theorem set_balance_le (F : Nat) (hF : F ≤ 32) (len : UInt32) (hl : len.toNat ≤ 64)
    (h : NearState) (key bs : List UInt8) (hb : bs.length = 16) :
    LookupMapInsertSome.cost401s cfg F 1 len h key bs ≤ 63000 * c + 4 * L +
      storageWriteUse h key (1 + (0 + 4 + len)).toNat 16 + registerLenUse h + readRegisterUse h 16 := by
  have hs := serialize_account_le cfg F hF len hl
  have hbS := serialize_balance_le cfg F hF
  have hk := concat_key_le cfg F hF len hl
  have hr := read_reg_le cfg F hF h StorageWrite.evictedRegister bs (by omega)
  rw [hb] at hr
  simp only [LookupMapInsertSome.cost401s]
  omega

theorem predecessor_le (F : Nat) (hF : F ≤ 32) (h : NearState)
    (ha : h.context.predecessorAccountId.length ≤ 64) :
    PredecessorId.cost526 cfg F h ≤ 23000 * c + L + predecessorUse h + registerLenUse h +
      readRegisterUse h h.context.predecessorAccountId.length := by
  have heq : predecessorHost h 0 = h.setRegister 0 h.context.predecessorAccountId := by
    simp [predecessorHost, u64Max]
  have hr := read_reg_le cfg F hF h 0 h.context.predecessorAccountId ha
  simp only [UInt64.toNat_zero, ← heq] at hr
  have hf : FromUtf8.cost927 h.context.predecessorAccountId.length ≤ 6500 := by
    simp only [FromUtf8.cost927]; omega
  have hfGas := Nat.mul_le_mul_right c hf
  simp only [PredecessorId.cost526]
  omega

theorem read_state_le (h : NearState) (s : WNear.State) :
    FtTotalSupply.cost219 cfg h s ≤ 12000 * c + 2 * L +
      storageReadUse h StateRead.stateKey 5 + registerLenUse h + readRegisterUse h 29 := by
  have ha := FtTotalSupplyMethod.c161 cfg
  have hz := FtTotalSupplyMethod.c687 cfg
  simp only [FtTotalSupply.cost219, StorageReadWrap.costS, ReadRegister.costRest,
    StateReadModel.header_length]
  change 105 * c + (40 * c + (249 * c + storageReadUse h StateRead.stateKey 5) +
    (70 * c + (281 * c + registerLenUse h + (95 * c + VecFromElem.cost687 cfg 0 (UInt32.ofNat 29) +
      (237 * c + readRegisterUse h 29))))) + BorshContract.cost161 cfg 1 + 726 * c + 334 * c ≤ _
  omega

theorem write_state_le (h : NearState) :
    DepositBody234.cost220B cfg h ≤ 16000 * c + 2 * L + storageWriteUse h StateRead.stateKey 5 29 := by
  have hw := walk_le cfg 18 (by decide)
  simp only [DepositBody234.cost220B, BorshSer.cost48]
  norm_num [MemCpy.cost]
  omega

end WNear.Binary.NearDepositGas
