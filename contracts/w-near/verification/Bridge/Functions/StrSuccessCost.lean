import Bridge.Functions.ParseEscapeFast

/-!
# Cost of the successful string loop

The scan and append are charged per segment. Error construction is absent, and
UTF-8 validation is charged only when the loop stops, rather than per escape.
The scratch-growth and copying costs retain their exact existing contracts.
-/

namespace WNear.Binary.ParseStrSuccess

open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseEscape (escDecode escK)
open WNear.Binary.ScratchGrow (capAfter fAfter costExt)
open WNear.Binary.FromUtf8 (cost927)

/-- Successful escape work, excluding all error-path reserves. -/
def costEsc (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc rest : List UInt8) (_L : Nat) : Nat :=
  ParseEscapeFast.cost649 cfg F cap acc rest

/-- Plain bytes are appended at an escape, or at the end of a copied string.
A borrowed string's terminal segment never calls the scratch append. -/
def baseAppend (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) : Nat :=
  if (l.dropWhile plain).head? = some 0x5C then
    ScratchFast.extCost cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)
  else if acc = [] then 0
  else ScratchFast.extCost cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)

/-- One scan and plain-byte append, with validation only at the final segment. -/
def costBase (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (_L : Nat) : Nat :=
  (300 + 30 * (l.takeWhile plain).length) * cfg.regularOpCost +
    baseAppend cfg F cap acc l +
    if (l.dropWhile plain).head? = some 0x5C then 0
    else cost927 (acc.length + (l.takeWhile plain).length) * cfg.regularOpCost

/-- The cost of `parse_str`'s run over `l`. -/
def costRun (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) : Nat :=
  let body := l.takeWhile plain
  let base := costBase cfg F cap acc l L
  match h : l.dropWhile plain with
  | [] => base
  | x :: rest =>
    if x = 0x5C then
      let cap1 := capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)
      let F1 := fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)
      base + costEsc cfg F1 cap1 (acc ++ body) rest L +
        match he : escDecode rest with
        | some (out, m) =>
          costRun cfg (fAfter F1 cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length))
            (capAfter cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length)) (acc ++ body ++ out)
            (rest.drop m) L
        | none => 0
    else base
termination_by l.length
decreasing_by
  have h1 := dropWhile_length_le l plain
  rw [h] at h1
  simp at h1
  simp only [List.length_drop]
  omega

theorem costRun_stop (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat)
    (h : ∀ rest, l.dropWhile plain ≠ 0x5C :: rest) :
    costRun cfg F cap acc l L = costBase cfg F cap acc l L := by
  rw [costRun]
  split
  · rfl
  · rename_i x rest hd
    have : x ≠ 0x5C := fun e => h rest (by rw [hd, e])
    simp only [this, ite_false]

theorem costRun_esc (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l rest : List UInt8) (L : Nat)
    (h : l.dropWhile plain = 0x5C :: rest) :
    costRun cfg F cap acc l L = costBase cfg F cap acc l L +
      costEsc cfg (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
        (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
        (acc ++ l.takeWhile plain) rest L +
      match escDecode rest with
      | some (out, m) =>
        costRun cfg
          (fAfter (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat out.length))
          (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat out.length))
          (acc ++ l.takeWhile plain ++ out) (rest.drop m) L
      | none => 0 := by
  rw [costRun]
  split
  · rename_i hd; rw [hd] at h; simp at h
  · rename_i x rest' hd
    rw [hd] at h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [ite_true]
    congr 1
    split <;> simp_all

theorem costBase_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) :
    costBase cfg F cap acc l L ≤ costRun cfg F cap acc l L := by
  cases hd : l.dropWhile plain with
  | nil => rw [costRun_stop cfg F cap acc l L (by intro r; rw [hd]; simp)]
  | cons x rest =>
    by_cases hx : x = 0x5C
    · subst hx; rw [costRun_esc cfg F cap acc l rest L hd]; omega
    · rw [costRun_stop cfg F cap acc l L (by intro r; rw [hd]; simp; intro e; exact absurd e hx)]


/-- The instruction reserve available at every loop head. -/
theorem scan_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) :
    (300 + 30 * (l.takeWhile plain).length) * cfg.regularOpCost ≤ costRun cfg F cap acc l L := by
  apply Nat.le_trans _ (costBase_le cfg F cap acc l L)
  unfold costBase
  omega

/-- At an escape the loop does no UTF-8 validation. -/
theorem costBase_esc (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l rest : List UInt8) (L : Nat)
    (h : l.dropWhile plain = 0x5C :: rest) :
    costBase cfg F cap acc l L = (300 + 30 * (l.takeWhile plain).length) * cfg.regularOpCost +
      ScratchFast.extCost cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) := by
  simp [costBase, baseAppend, h]

/-- At a closing quote validation is charged exactly once, on the decoded bytes. -/
theorem costBase_close (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l rest : List UInt8) (L : Nat)
    (h : l.dropWhile plain = 0x22 :: rest) :
    costBase cfg F cap acc l L =
      (300 + 30 * (l.takeWhile plain).length + cost927 (acc.length + (l.takeWhile plain).length)) * cfg.regularOpCost +
      (if acc = [] then 0 else
        ScratchFast.extCost cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)) := by
  simp [costBase, baseAppend, h, Nat.add_mul]
  omega

end WNear.Binary.ParseStrSuccess
