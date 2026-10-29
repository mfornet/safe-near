import Bridge.Methods.NewGas
import Bridge.Methods.NearDepositRuns
import Bridge.Methods.NearDepositLogPre

/-!
# Uniform operation bounds for initialized deposit

Separate bounded allocator and formatting work from the host charges. These bounds
apply to every amount and to every free-list size the method reaches.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem walk_le (F : Nat) (hF : F ≤ 32) : AllocWalk.walkCost cfg F ≤ 10570 * c := by
  have hw := AllocWalk.wc_mono cfg hF
  simp only [AllocWalk.walkCost, AllocWalk.wc] at *
  omega

/-- All deposit allocations fit a page and inspect at most 32 free cells. -/
theorem alloc_le (F : Nat) (hF : F ≤ 32) (s : UInt32) (hs : s.toNat ≤ 4096) :
    VecWithCap.costAllocF cfg F s ≤ 12000 * c + L := by
  have hp := NewGas.pages1 s hs
  have hw := walk_le cfg F hF
  unfold VecWithCap.costAllocF
  split
  · simp only [VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581, hp]
    omega
  · simp only [AllocWalk.cost310W, hp]
    omega

/-- One append to the deposit log, including its possible reallocation. -/
theorem sink_le (F k : Nat) (hF : F ≤ 30) (hk : k ≤ 120) :
    StrSinkMulti.costS cfg F 120 k ≤ 18000 * c + L := by
  have hw := walk_le cfg (max F 1 + 1) (by omega)
  have hm := FtTotalSupplyMethod.memcpy_le k
  have hmk : MemCpy.cost k ≤ 2166 := by omega
  have hmGas := Nat.mul_le_mul_right c hmk
  have ha : activationGas c (entryLocals f841 [.i32 0, .i32 0, .i32 0]) ≤ 40 * c := by
    simp [activationGas, entryLocals, f841, ValType.default]
    try omega
  simp only [StrSinkMulti.costS, StrSinkMulti.gmax]
  norm_num [MemCpy.cost] at *
  omega

/-- Both arguments and pieces of the deposit log have bounded formatting work. -/
theorem log_format_le (F : Nat) (hF : F ≤ 30) (lo hi : UInt64) (alen : UInt32) (ha : alen.toNat ≤ 64) :
    DepositLog.cost872 cfg F lo hi alen ≤ 140000 * c + 7 * L := by
  have hd := FmtString.decDigits_le lo hi
  have hs1 := sink_le cfg F 9 hF (by decide)
  have hs2 := sink_le cfg F (FmtDigits.decDigits (FmtU128.val lo hi)).length hF (by omega)
  have hs3 := sink_le cfg F alen.toNat hF (by omega)
  have hf := Nat.mul_le_mul_right c (FtTotalSupplyMethod.fmt_le lo hi)
  simp only [DepositLog.cost872, FmtWriteN.costN, DepositLog.Ka, DepositLog.KB,
    DepositLog.Kb, DepositLog.K901, DepositLog.K179, FmtStrPad.cost179, FmtStrPad.cost923, FmtStrPad.cost856]
  simp [activationGas, entryLocals, f840, f901, f179, f779, f923, f856, ValType.default]
  omega

/-- Formatting the complete log includes one allocation before the piece/argument loop. -/
theorem log_allocation_le (F : Nat) (hF : F ≤ 30) (lo hi : UInt64) (alen : UInt32) (ha : alen.toNat ≤ 64) :
    FmtFormat.cost846 cfg F 2 17 (DepositLog.cost872 cfg F lo hi alen) ≤ 160000 * c + 8 * L := by
  have hf := log_format_le cfg F hF lo hi alen ha
  have hal := alloc_le cfg F (by omega) (34 : UInt32) (by decide)
  simp only [FmtFormat.cost846]
  simp [activationGas, entryLocals, f310, f872, ValType.default]
  omega

/-- The method's successful tail: bounded work and the exact log host charge. -/
theorem tail_le (F : Nat) (hF : F ≤ 30) (lo hi : UInt64) (ab : List UInt8) (ha : ab.length ≤ 64)
    (h : NearState) :
    DepositTail.costTail cfg F lo hi ab h ≤ 170000 * c + 8 * L + logUtf8Use h (DepositTail.logText lo hi ab).length := by
  have hal : (UInt32.ofNat ab.length).toNat ≤ 64 := by simp; omega
  have hf := log_allocation_le cfg F hF lo hi (UInt32.ofNat ab.length) hal
  simp only [DepositTail.costTail, DepositTail.logText]
  simp [activationGas, entryLocals, f354, f745, f846, f779, f546, f68, ValType.default]
  omega

end WNear.Binary.NearDepositGas
