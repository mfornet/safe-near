import Bridge.Functions.StrCost
import Mathlib.Tactic.Ring

/-!
# The all-outcome string bound cannot supply a linear accepting bound

Every escape in `costRun` reserves eight error constructions. Each error's
position scan is linear in the whole input. A run of valid newline escapes
therefore has a quadratic lower bound in this cost expression. This is a
property of the existing bound, not of the binary's actual accepting gas.
-/

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near
open WNear.Binary.ParseEscape (escDecode)

/-- An input body consisting of newline escapes and its terminating quote. -/
def newlineEscapes : Nat → List UInt8
  | 0 => [0x22]
  | n + 1 => 0x5C :: 0x6E :: newlineEscapes n

@[simp] theorem newlineEscapes_length (n : Nat) : (newlineEscapes n).length = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [newlineEscapes, ih]; omega

/-- These inputs reach the run's accepting outcome, with exactly the decoded newlines. -/
theorem strRun_newlineEscapes (n : Nat) (acc : List UInt8) :
    strRun (newlineEscapes n) acc = .ok (acc ++ List.replicate n 10) [] := by
  induction n generalizing acc with
  | zero =>
    rw [strRun_cons _ _ 0x22 [] (by simp [newlineEscapes, plain])]
    simp [newlineEscapes, plain]
  | succ n ih =>
    rw [strRun_cons _ _ 0x5C (0x6E :: newlineEscapes n) (by simp [newlineEscapes, plain])]
    simp only [show (0x5C : UInt8) ≠ 0x22 by decide, ite_false, ite_true]
    have he : escDecode (0x6E :: newlineEscapes n) = some ([10], 1) := by rfl
    rw [he]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [show (newlineEscapes (n + 1)).takeWhile plain = [] by simp [newlineEscapes, plain]]
    simp only [List.append_nil]
    rw [ih]
    simp [List.replicate_succ, List.append_assoc]

/-- The decoded newline bytes are valid UTF-8 for every escape count. -/
theorem newlineEscapes_utf8 (n : Nat) : Utf8.utf8Ok (List.replicate n 10) = true := by
  induction n with
  | zero => simp [Utf8.utf8Ok]
  | succ n ih =>
    rw [List.replicate_succ, Utf8.utf8Ok_ascii 10 _ (by decide), ih]

/-- The JSON string model accepts every member of this cost-witness family. -/
theorem newlineEscapes_model (n : Nat) :
    ∃ s : String, NearInterface.Json.stringBody (newlineEscapes n) [] = some (some s, []) ∧
      s.toByteArray = (List.replicate n (10 : UInt8)).toByteArray := by
  have h := str_model (newlineEscapes n)
  rw [strRun_newlineEscapes, List.nil_append] at h
  simpa only [newlineEscapes_utf8, ite_true] using h

/-- A reserved syntax error includes a position scan costing at least 50 ops per input byte. -/
theorem costErr_scan_lower (cfg : WasmConfig) (F L : Nat) :
    50 * L * cfg.regularOpCost ≤ SerdeErrBox.costErr cfg F L := by
  unfold SerdeErrBox.costErr SerdePosition.cost638 SerdePosition.cost645
  simp only [Nat.add_mul]
  omega

/-- Every escape reserves this much, even when the escape succeeds. -/
theorem costEsc_scan_lower (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (acc rest : List UInt8) (L : Nat) :
    (3000 + 400 * L) * cfg.regularOpCost ≤ costEsc cfg F cap acc rest L := by
  have h := Nat.mul_le_mul_left 8 (costErr_scan_lower cfg F L)
  unfold costEsc
  simp only [Nat.add_mul, ← Nat.mul_assoc] at h ⊢
  simp only [Nat.reduceMul] at h
  omega

/-- The existing all-outcome bound reserves a whole-input error scan for every valid escape. -/
theorem costRun_newlineEscapes_lower (cfg : WasmConfig) (n F : Nat) (cap : UInt32)
    (acc : List UInt8) (L : Nat) :
    n * ((3000 + 400 * L) * cfg.regularOpCost) ≤ costRun cfg F cap acc (newlineEscapes n) L := by
  induction n generalizing F cap acc with
  | zero => simp
  | succ n ih =>
    rw [costRun_esc cfg F cap acc (newlineEscapes (n + 1)) (0x6E :: newlineEscapes n) L
      (by simp [newlineEscapes, plain])]
    have he : escDecode (0x6E :: newlineEscapes n) = some ([10], 1) := by rfl
    rw [he]
    simp only [List.drop_succ_cons, List.drop_zero]
    have hesc := costEsc_scan_lower cfg
      (ScratchGrow.fAfter F cap (UInt32.ofNat acc.length)
        (UInt32.ofNat ((newlineEscapes (n + 1)).takeWhile plain).length))
      (ScratchGrow.capAfter cap (UInt32.ofNat acc.length)
        (UInt32.ofNat ((newlineEscapes (n + 1)).takeWhile plain).length))
      (acc ++ (newlineEscapes (n + 1)).takeWhile plain) (0x6E :: newlineEscapes n) L
    have hrec := ih
      (ScratchGrow.fAfter
        (ScratchGrow.fAfter F cap (UInt32.ofNat acc.length)
          (UInt32.ofNat ((newlineEscapes (n + 1)).takeWhile plain).length))
        (ScratchGrow.capAfter cap (UInt32.ofNat acc.length)
          (UInt32.ofNat ((newlineEscapes (n + 1)).takeWhile plain).length))
        (UInt32.ofNat (acc ++ (newlineEscapes (n + 1)).takeWhile plain).length) (UInt32.ofNat [10].length))
      (ScratchGrow.capAfter
        (ScratchGrow.capAfter cap (UInt32.ofNat acc.length)
          (UInt32.ofNat ((newlineEscapes (n + 1)).takeWhile plain).length))
        (UInt32.ofNat (acc ++ (newlineEscapes (n + 1)).takeWhile plain).length) (UInt32.ofNat [10].length))
      (acc ++ (newlineEscapes (n + 1)).takeWhile plain ++ [10])
    rw [Nat.succ_mul]
    omega

/-- At the actual input length, the bound grows at least quadratically in the escape count. -/
theorem costRun_newlineEscapes_quadratic (cfg : WasmConfig) (n F : Nat) (cap : UInt32) :
    (800 * n * n + 3400 * n) * cfg.regularOpCost ≤
      costRun cfg F cap [] (newlineEscapes n) (newlineEscapes n).length := by
  have h := costRun_newlineEscapes_lower cfg n F cap [] (newlineEscapes n).length
  rw [newlineEscapes_length] at h
  rw [newlineEscapes_length]
  convert h using 1 <;> ring

end WNear.Binary.ParseStr
