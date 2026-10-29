import Bridge.Methods.NearDepositCostBody

/-!
# Protocol bounds on deposit's host fees

Separate the three write paths from value-independent host charges. The final
numeric bounds use the same protocol-86 constants as the other method proofs.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open Near.TrieOverlay
open WNear.Binary.FtTotalSupplyMethod (CostsV86)
open WNear.Binary.NewMethod (CostsNewV86)

structure CostsDepositV86 (p : RuntimeConfig) : Prop extends CostsNewV86 p where
  writeEvictedByte : p.wasm.extCosts.cost "storage_write_evicted_byte" ≤ 32117307
  logBase : p.wasm.extCosts.cost "log_base" ≤ 3543313050
  logByte : p.wasm.extCosts.cost "log_byte" ≤ 13198791
  logCount : 1 ≤ p.wasm.limits.maxNumberLogs

def writeFees (h : NearState) (k v b : Nat) : Nat :=
  chargesUse h (storageWriteBeforeCharges k v) + chargesUse h [.ext "storage_write_evicted_byte" b] +
    chargesUse h (writeReg b)

def methodFees (h : NearState) : Nat :=
  attachedDepositUse h + chargesUse h (predecessorChargeList 64) +
    chargesUse h (storageHasKeyBeforeCharges 69) + readAllowance h 69 16 + 2 * writeFees h 69 16 16 +
    4 * registerLenUse h + readRegisterUse h 64 + 2 * readRegisterUse h 16 +
    panicUtf8Use h 163 + logUtf8Use h 120 + readAllowance h 5 29 + readRegisterUse h 29 + writeFees h 5 29 29

theorem methodHost_mono (h : NearState) (key : List UInt8) {a b : Nat} (hab : a ≤ b) :
    methodHost h key a ≤ methodHost h key b := by
  have hm := Nat.mul_le_mul_left (h.extCosts.cost "read_memory_byte") hab
  have hh := Nat.mul_le_mul_left (h.extCosts.cost "storage_has_key_byte") hab
  have hr := Nat.mul_le_mul_left (h.extCosts.cost "storage_read_key_byte") hab
  have hw := Nat.mul_le_mul_left (h.extCosts.cost "storage_write_key_byte") hab
  simp only [methodHost, bodyHost, readAllowance, writeAllowance, storageHasKeyBeforeCharges,
    storageReadBeforeCharges, storageWriteBeforeCharges, chargesUse, chargeUse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem readRegisterUse_mono (h : NearState) {a b : Nat} (hab : a ≤ b) :
    readRegisterUse h a ≤ readRegisterUse h b := by
  have hr := Nat.mul_le_mul_left (h.extCosts.cost "read_register_byte") hab
  have hw := Nat.mul_le_mul_left (h.extCosts.cost "write_memory_byte") hab
  simp only [readRegisterUse, readRegisterChargeList, chargesUse, chargeUse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The host allowance is fixed fees plus exactly the three mutation paths. -/
theorem methodHost_fees (h : NearState) (key : List UInt8) (n : Nat) (hn : n ≤ 69)
    (ha : h.context.predecessorAccountId.length ≤ 64) :
    methodHost h key n ≤ methodFees h +
      2 * ((2 * (contractKey h.context.currentAccountId key).length + 2) * trieNodeMax h) +
      (2 * (contractKey h.context.currentAccountId StateRead.stateKey).length + 2) * trieNodeMax h := by
  have hm := methodHost_mono h key hn
  have hr := readRegisterUse_mono h ha
  have hp := Nat.mul_le_mul_left (h.extCosts.cost "write_register_byte") ha
  simp only [methodHost, bodyHost, methodFees, writeAllowance, writeFees] at hm ⊢
  have hpred : predecessorUse h ≤ chargesUse h (predecessorChargeList 64) := by
    simp only [predecessorUse, predecessorChargeList, chargesUse, chargeUse,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  omega

/-- All non-trie host charges fit comfortably within the compute allowance. -/
theorem methodFees_le (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (hc : CostsV86 ctx.protocol) (hd : CostsDepositV86 ctx.protocol) :
    methodFees (erase (hostOf ctx raw)) ≤ 2000000000000 := by
  have hx : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  simp only [methodFees, readAllowance, writeFees, attachedDepositUse, attachedDepositChargeList,
    predecessorChargeList, storageHasKeyBeforeCharges, storageReadBeforeCharges, storageReadValueCharges,
    storageWriteBeforeCharges, writeReg, registerLenUse, registerLenChargeList, readRegisterUse, readRegisterChargeList,
    panicUtf8Use, panicUtf8Charges, logUtf8Use, logUtf8Charges, chargesUse, chargeUse, hx,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num
  simp only [chargeUse, hx]
  have := hc.base; have := hc.readMemoryBase; have := hc.readMemoryByte
  have := hc.writeMemoryBase; have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  have := hd.storageHasKeyBase; have := hd.storageHasKeyByte; have := hd.storageWriteBase
  have := hd.storageWriteKeyByte; have := hd.storageWriteValueByte; have := hd.writeEvictedByte
  have := hd.logBase; have := hd.logByte
  omega

end WNear.Binary.NearDepositGas
