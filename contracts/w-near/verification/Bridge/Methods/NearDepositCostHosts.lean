import Bridge.Methods.NearDepositCostCalls
import Bridge.Methods.NearDepositCostPanics

/-!
# Value-independent host allowances for deposit

Read calls at the boundary bill no trie nodes. Each write bills one bounded
lookup/dereference path, independent of whether the old account value is present.
Keeping that path separate avoids counting mutually exclusive branches twice.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open Near.TrieOverlay

def readAllowance (h : NearState) (k b : Nat) : Nat :=
  chargesUse h (storageReadBeforeCharges k) + chargesUse h (storageReadValueCharges b) + chargesUse h (writeReg b)

def writeAllowance (h : NearState) (key : List UInt8) (k v b : Nat) : Nat :=
  chargesUse h (storageWriteBeforeCharges k v) +
    (2 * (contractKey h.context.currentAccountId key).length + 2) * trieNodeMax h +
    chargesUse h [.ext "storage_write_evicted_byte" b] + chargesUse h (writeReg b)

theorem read_allowance (h : NearState) (key : List UInt8) (k b : Nat)
    (ht : h.storageReadsFromTrie = false) (hsmall : b ≤ 4000) (hb : ∀ v, h.storage key = some v → v.length ≤ b) :
    storageReadUse h key k ≤ readAllowance h k b := by
  have hn := readNodes_of_false ht (contractKey h.context.currentAccountId key)
  cases hv : h.storage key with
  | none =>
    simp only [storageReadUse, storageReadPhaseUse, hv, hn, readAllowance, Option.map_none,
      Option.getD_none, Nat.zero_mul, Nat.zero_add, chargesUse, List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  | some v =>
    have hl := hb v hv
    have hs1 : ¬v.length > 4000 := by omega
    have hs2 : ¬b > 4000 := by omega
    have hr := Nat.mul_le_mul_left (h.extCosts.cost "storage_read_value_byte") hl
    have hw := Nat.mul_le_mul_left (h.extCosts.cost "write_register_byte") hl
    simp only [storageReadUse, storageReadPhaseUse, hv, hn, readAllowance, Option.map_some,
      Option.getD_some, Nat.zero_mul, Nat.zero_add, storageReadValueCharges, writeReg, chargesUse,
      chargeUse, hs1, hs2, ite_false, List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem write_allowance (h : NearState) (key : List UInt8) (k v b : Nat)
    (hb : ∀ old, h.storage key = some old → old.length ≤ b) :
    storageWriteUse h key k v ≤ writeAllowance h key k v b := by
  cases hv : h.storage key with
  | none =>
    simp only [storageWriteUse, storageWritePhaseUse, storageWriteAfter, hv, writeAllowance,
      Option.map_none, Option.getD_none, chargesUse, List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  | some old =>
    have hl := hb old hv
    have he := Nat.mul_le_mul_left (h.extCosts.cost "storage_write_evicted_byte") hl
    have hw := Nat.mul_le_mul_left (h.extCosts.cost "write_register_byte") hl
    simp only [storageWriteUse, storageWritePhaseUse, storageWriteAfter, hv, writeAllowance,
      Option.map_some, Option.getD_some, writeReg, chargesUse, chargeUse,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem log_use_mono (h : NearState) {a b : Nat} (hab : a ≤ b) : logUtf8Use h a ≤ logUtf8Use h b := by
  have hr := Nat.mul_le_mul_left (h.extCosts.cost "read_memory_byte") hab
  have hu := Nat.mul_le_mul_left (h.extCosts.cost "utf8_decoding_byte") hab
  have hl := Nat.mul_le_mul_left (h.extCosts.cost "log_byte") hab
  simp only [logUtf8Use, logUtf8Charges, chargesUse, chargeUse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem panic_use_mono (h : NearState) {a b : Nat} (hab : a ≤ b) : panicUtf8Use h a ≤ panicUtf8Use h b := by
  have hr := Nat.mul_le_mul_left (h.extCosts.cost "read_memory_byte") hab
  have hu := Nat.mul_le_mul_left (h.extCosts.cost "utf8_decoding_byte") hab
  simp only [panicUtf8Use, panicUtf8Charges, chargesUse, chargeUse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

end WNear.Binary.NearDepositGas
