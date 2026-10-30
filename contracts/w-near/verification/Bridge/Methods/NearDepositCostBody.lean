import Bridge.Methods.NearDepositCostHosts

/-!
# The initialized deposit's branch costs

Bound success and overflow work by one common allowance. Its write component has
one trie path, so callers can reserve two account writes for registration and minting.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open WNear.Binary.NewBody (keep)

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem kPos_le (F : Nat) (hF : F ≤ 27) (h : NearState) :
    DepositPanicsFull.kPos cfg F (keep h) ≤ 410000 * c + 20 * L + panicUtf8Use h 163 := by
  have hb := begin_le cfg F (by omega) NearDepositPanics.textPositive
    (by rw [DepositPanicsFull.textPos_length]; decide) h
  have hm := panic_use_mono h (by decide : 68 ≤ 163)
  simp only [DepositPanicsFull.textPos_length] at hb
  simp only [DepositPanicsFull.kPos, DepositPanicsFull.cost664_keep, DepositPanicsFull.textPos_eq]
  omega

theorem kSmall_le (F : Nat) (hF : F ≤ 27) (h : NearState) :
    DepositPanicsFull.kSmall cfg F (keep h) ≤ 410000 * c + 20 * L + panicUtf8Use h 163 := by
  have hb := begin_le cfg F (by omega) NearDepositPanics.textTooSmall
    (by rw [DepositPanicsFull.textSmall_length]; decide) h
  have hm := panic_use_mono h (by decide : 56 ≤ 163)
  simp only [DepositPanicsFull.textSmall_length] at hb
  simp only [DepositPanicsFull.kSmall, DepositPanicsFull.cost664_keep, DepositPanicsFull.textSmall_eq]
  omega

theorem kSup_le (F : Nat) (hF : F ≤ 26) (h : NearState) :
    DepositPanicsFull.kSup cfg F (keep h) ≤ 600000 * c + 30 * L + panicUtf8Use h 163 := by
  have hb := supply_le cfg F (by omega) NearDepositPanics.textSupply
    (by rw [DepositPanicsFull.textSup_length]) h
  simp only [DepositPanicsFull.textSup_length] at hb
  simp only [DepositPanicsFull.kSup, DepositPanicsFull.cost879_keep, DepositPanicsFull.textSup_eq]
  exact hb

def segmentHost (h : NearState) (key : List UInt8) (n : Nat) : Nat :=
  readAllowance h n 16 + writeAllowance h key n 16 16 +
    2 * registerLenUse h + 2 * readRegisterUse h 16 + panicUtf8Use h 163 + logUtf8Use h 120

/-- One minting segment covers its success, balance overflow and supply overflow paths. -/
theorem segment_le (F : Nat) (hF : F ≤ 7) (h : NearState) (key : List UInt8)
    (ht : h.storageReadsFromTrie = false) (hb : ∀ v, h.storage key = some v → v.length ≤ 16)
    (x0 x1 t0 t1 lo hi : UInt64) (ab : List UInt8) (ha : ab.length ≤ 64) :
    DepositSegAll.costSegAll cfg F 1 (UInt32.ofNat ab.length) h key x0 x1 t0 t1 lo hi ab
      (DepositPanicsFull.kSup cfg) ≤ 730000 * c + 40 * L +
        segmentHost h key (1 + (0 + 4 + UInt32.ofNat ab.length)).toNat := by
  have hl : (UInt32.ofNat ab.length).toNat ≤ 64 := by simp; omega
  have hold : (storeBytes (.i64 x0) 8 ++ storeBytes (.i64 x1) 8).length = 16 := by simp
  have hg := get_balance_le cfg F (by omega) (UInt32.ofNat ab.length) hl h key _ hold
  have hw := set_balance_le cfg (F + 3) (by omega) (UInt32.ofNat ab.length) hl h key _ hold
  have hr := read_allowance h key (1 + (0 + 4 + UInt32.ofNat ab.length)).toNat 16 ht (by decide) hb
  have hwa := write_allowance h key (1 + (0 + 4 + UInt32.ofNat ab.length)).toNat 16 16 hb
  have htail := tail_le cfg (F + 7) (by omega) lo hi ab ha h
  have hlog := log_use_mono h (NearDepositMethod.deposit_log_length lo hi ab ha).2
  have hpanic := panic_use_mono h (by decide : 16 ≤ 163)
  have hsup := kSup_le cfg (F + 7) (by omega) h
  simp only [DepositSegAll.costSegAll, DepositSeg.costSeg, InternalDepositOverflow.cost406sup,
    InternalDepositOverflow.cost406bal, segmentHost]
  simp [activationGas, entryLocals, f406, f879, ValType.default] at *
  split_ifs <;> omega

def bodyHost (h : NearState) (key : List UInt8) (n : Nat) : Nat :=
  attachedDepositUse h + predecessorUse h + chargesUse h (storageHasKeyBeforeCharges n) +
    readAllowance h n 16 + 2 * writeAllowance h key n 16 16 +
    3 * registerLenUse h + readRegisterUse h h.context.predecessorAccountId.length +
    2 * readRegisterUse h 16 + panicUtf8Use h 163 + logUtf8Use h 120

/-- The full 232 body, on every initialized path, with at most two account-write paths. -/
theorem body232_le (h : NearState) (key : List UInt8) (reg : Option (UInt64 × UInt64))
    (xb : List UInt8) (t0 t1 : UInt64) (ha : h.context.predecessorAccountId.length ≤ 64)
    (ht : h.storageReadsFromTrie = false) (hb : ∀ v, h.storage key = some v → v.length ≤ 16) :
    DepositBody.cost232 cfg 2 1 h key reg xb t0 t1
      (DepositPanicsFull.kSup cfg) (DepositPanicsFull.kSmall cfg) (DepositPanicsFull.kPos cfg) ≤
        850000 * c + 50 * L + bodyHost h key
          (1 + (0 + 4 + UInt32.ofNat h.context.predecessorAccountId.length)).toNat := by
  let len := UInt32.ofNat h.context.predecessorAccountId.length
  let n := (1 + (0 + 4 + len)).toNat
  have hl : len.toNat ≤ 64 := by simp [len]; omega
  have hp := predecessor_le cfg 2 (by decide) h ha
  have hc := contains_le cfg 2 (by decide) len hl (predecessorHost h 0) key
  have hh : storageHasKeyUse (predecessorHost h 0) key n = chargesUse h (storageHasKeyBeforeCharges n) := by
    rw [DepositCosts.storageHasKeyUse_congr (DepositBody.keep_predecessorHost h) key n]
    simp only [storageHasKeyUse, readNodes_of_false ht, Nat.zero_mul, Nat.add_zero]
  change LookupMapContains.cost394 cfg 2 1 len (predecessorHost h 0) key ≤
    32000 * c + 2 * L + storageHasKeyUse (predecessorHost h 0) key n at hc
  rw [hh] at hc
  have hkp := kPos_le cfg 2 (by decide) h
  have hks := kSmall_le cfg 4 (by decide) h
  have hwrite := write_allowance h key n 16 16 hb
  have hregister := register_le cfg 4 (by decide) len hl h key
  by_cases hd : DepositBody.depOf h = 0
  · simp only [DepositBody.cost232, hd, ite_true, DepositBody.costPos, bodyHost]
    omega
  · cases reg with
    | some words =>
      rcases words with ⟨x0, x1⟩
      have hs := segment_le cfg 4 (by decide) h key ht hb x0 x1 t0 t1
        (EnvGetters.depLo h) (EnvGetters.depHi h) h.context.predecessorAccountId ha
      simp only [DepositBody.cost232, hd, ite_false, DepositBody.costReg, bodyHost, segmentHost] at *
      change _ ≤ 850000 * c + 50 * L + (attachedDepositUse h + predecessorUse h +
        chargesUse h (storageHasKeyBeforeCharges n) + readAllowance h n 16 + 2 * writeAllowance h key n 16 16 +
        3 * registerLenUse h + readRegisterUse h h.context.predecessorAccountId.length +
        2 * readRegisterUse h 16 + panicUtf8Use h 163 + logUtf8Use h 120)
      simp only [len, n, Nat.reduceAdd] at *
      omega
    | none =>
      have hbNew : ∀ v, (DepositBody.withVal h key DepositBody.zeros).storage key = some v → v.length ≤ 16 := by
        intro v hv
        simp only [DepositBody.withVal, ite_true, Option.some.injEq] at hv
        subst v
        norm_num [DepositBody.zeros]
      have hs := segment_le cfg 7 (by decide) (DepositBody.withVal h key DepositBody.zeros) key ht hbNew
        0 0 t0 t1 (DepositBody.aloOf h xb) (DepositBody.ahiOf h xb) h.context.predecessorAccountId ha
      change DepositSegAll.costSegAll cfg 7 1 len (DepositBody.withVal h key DepositBody.zeros) key
        0 0 t0 t1 (DepositBody.aloOf h xb) (DepositBody.ahiOf h xb) h.context.predecessorAccountId
        (DepositPanicsFull.kSup cfg) ≤ 730000 * c + 40 * L + segmentHost h key n at hs
      simp only [DepositBody.cost232, hd, ite_false, DepositBody.costUnreg, bodyHost, segmentHost] at *
      simp only [len, n, Nat.reduceAdd] at *
      split_ifs <;> omega

def methodHost (h : NearState) (key : List UInt8) (n : Nat) : Nat :=
  bodyHost h key n + readAllowance h 5 29 + registerLenUse h + readRegisterUse h 29 +
    writeAllowance h StateRead.stateKey 5 29 29

/-- All initialized paths of 234: bounded Wasm work and the three write-path allowances. -/
theorem body234_le (h : NearState) (s : WNear.State) (reg : Option (UInt64 × UInt64))
    (ha : h.context.predecessorAccountId.length ≤ 64) (ht : h.storageReadsFromTrie = false)
    (hv : h.storage StateRead.stateKey = some (WNear.header s))
    (hb : ∀ v, h.storage (DepositBody234.keyOf h) = some v → v.length ≤ 16) :
    DepositBody234.cost234 cfg h s reg (DepositPanicsFull.kSup cfg)
      (DepositPanicsFull.kSmall cfg) (DepositPanicsFull.kPos cfg) ≤ 900000 * c + 54 * L +
        methodHost h (DepositBody234.keyOf h)
          (1 + (0 + 4 + UInt32.ofNat h.context.predecessorAccountId.length)).toNat := by
  have hs := read_state_le cfg h s
  have hw := write_state_le cfg h
  have hbState : ∀ v, h.storage StateRead.stateKey = some v → v.length ≤ 29 := by
    intro v he
    rw [hv] at he
    cases he
    rw [StateReadModel.header_length]
  have hr := read_allowance h StateRead.stateKey 5 29 ht (by decide) hbState
  have hwa := write_allowance h StateRead.stateKey 5 29 29 hbState
  have hbody := body232_le cfg h (DepositBody234.keyOf h) reg (WNear.Borsh.u64 s.accountStorageUsage)
    (FtTotalSupply.loOf s) (FtTotalSupply.hiOf s) ha ht hb
  simp only [DepositBody234.cost234, methodHost]
  omega

end WNear.Binary.NearDepositGas
