import Bridge.Functions.StrSuccessCost

/-! # Separating successful string work from scratch growth and copying -/

namespace WNear.Binary.ParseStrSuccess

open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseEscape (escDecode escK)
open WNear.Binary.ScratchGrow (capAfter fAfter costExt)
open WNear.Binary.FromUtf8 (cost927)

/-- The exact charge for appending a segment's plain bytes. -/
def appendBase (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (_L : Nat) : Nat :=
  baseAppend cfg F cap acc l

/-- The exact charge for appending one decoded escape. -/
def appendEsc (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (_L : Nat) : Nat :=
  ParseEscapeFast.appendCost cfg F cap acc l

/-- The cost of `parse_str`'s run over `l`. -/
def appendCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) : Nat :=
  let body := l.takeWhile plain
  let base := appendBase cfg F cap acc l L
  match h : l.dropWhile plain with
  | [] => base
  | x :: rest =>
    if x = 0x5C then
      let cap1 := capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)
      let F1 := fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)
      base + appendEsc cfg F1 cap1 (acc ++ body) rest L +
        match he : escDecode rest with
        | some (out, m) =>
          appendCost cfg (fAfter F1 cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length))
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

theorem appendCost_stop (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat)
    (h : ∀ rest, l.dropWhile plain ≠ 0x5C :: rest) :
    appendCost cfg F cap acc l L = appendBase cfg F cap acc l L := by
  rw [appendCost]
  split
  · rfl
  · rename_i x rest hd
    have : x ≠ 0x5C := fun e => h rest (by rw [hd, e])
    simp only [this, ite_false]

theorem appendCost_esc (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l rest : List UInt8) (L : Nat)
    (h : l.dropWhile plain = 0x5C :: rest) :
    appendCost cfg F cap acc l L = appendBase cfg F cap acc l L +
      appendEsc cfg (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
        (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
        (acc ++ l.takeWhile plain) rest L +
      match escDecode rest with
      | some (out, m) =>
        appendCost cfg
          (fAfter (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat out.length))
          (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat out.length))
          (acc ++ l.takeWhile plain ++ out) (rest.drop m) L
      | none => 0 := by
  rw [appendCost]
  split
  · rename_i hd; rw [hd] at h; simp at h
  · rename_i x rest' hd
    rw [hd] at h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [ite_true]
    congr 1
    split <;> simp_all


/-- All remaining work is linear; the separate append charge still needs amortization.
The returned suffix is strictly shorter than the input because the closing quote is consumed. -/
theorem costRun_linear_work (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (acc l bytes rest : List UInt8) (L : Nat) (hok : strRun l acc = .ok bytes rest) :
    rest.length < l.length ∧
    costRun cfg F cap acc l L ≤
      (400 + 450 * (l.length - rest.length) + 100 * acc.length) * cfg.regularOpCost +
        appendCost cfg F cap acc l L := by
  induction hn : l.length using Nat.strong_induction_on generalizing F cap acc l bytes rest with
  | _ len ih =>
    rw [← hn]
    have hsplit := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
    simp only [List.length_append] at hsplit
    cases hd : l.dropWhile plain with
    | nil => rw [strRun_nil _ _ hd] at hok; cases hok
    | cons x tail =>
      have hlength : l.length = (l.takeWhile plain).length + 1 + tail.length := by
        rw [hd] at hsplit
        simp only [List.length_cons] at hsplit
        omega
      rw [strRun_cons _ _ x tail hd] at hok
      by_cases h22 : x = 0x22
      · subst x
        simp only [ite_true, StrOut.ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨by omega, ?_⟩
        have hnosc : ∀ r, l.dropWhile plain ≠ 0x5C :: r := by intro r; rw [hd]; simp
        rw [costRun_stop cfg F cap acc l L hnosc, costBase_close cfg F cap acc l tail L hd,
          appendCost_stop cfg F cap acc l L hnosc]
        simp only [appendBase, baseAppend, hd, List.head?_cons, show (0x22 : UInt8) ≠ 0x5C by decide, ite_false]
        have hop : 300 + 30 * (l.takeWhile plain).length + cost927 (acc.length + (l.takeWhile plain).length) ≤
            400 + 450 * (l.length - tail.length) + 100 * acc.length := by
          unfold cost927
          omega
        exact Nat.add_le_add_right (Nat.mul_le_mul_right cfg.regularOpCost hop) _
      · simp only [h22, ite_false] at hok
        by_cases h92 : x = 0x5C
        · subst x
          simp only [ite_true] at hok
          cases he : escDecode tail with
          | none => simp [he] at hok
          | some p =>
            obtain ⟨eo, m⟩ := p
            simp only [he] at hok
            have hlen := escDecode_len tail eo m he
            have hshort : (tail.drop m).length < len := by simp only [List.length_drop]; omega
            have hrec := ih (tail.drop m).length hshort
              (fAfter (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length))
              (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length))
              (acc ++ l.takeWhile plain ++ eo) (tail.drop m) bytes rest hok rfl
            have hop :
                300 + 30 * (l.takeWhile plain).length + 200 * (m + 1) +
                  (400 + 450 * ((tail.drop m).length - rest.length) + 100 * (acc ++ l.takeWhile plain ++ eo).length) ≤
                400 + 450 * (l.length - rest.length) + 100 * acc.length := by
              simp only [List.length_drop, List.length_append] at *
              omega
            have hesc := ParseEscapeFast.cost649_le cfg
              (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
              (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
              (acc ++ l.takeWhile plain) tail eo m he
            refine ⟨by have := hrec.1; simp only [List.length_drop] at this; omega, ?_⟩
            rw [costRun_esc cfg F cap acc l tail L hd,
              costBase_esc cfg F cap acc l tail L hd, he,
              appendCost_esc cfg F cap acc l tail L hd, he]
            unfold costEsc appendBase appendEsc
            simp only [baseAppend, hd, List.head?_cons, ite_true, escK, he]
            have hprod := Nat.mul_le_mul_right cfg.regularOpCost hop
            simp only [Nat.add_mul] at hprod
            have hrec' := hrec.2
            simp only [Nat.add_mul] at hrec' hesc ⊢
            omega
        · simp [h92] at hok

end WNear.Binary.ParseStrSuccess
