import Bridge.Functions.StrModel
import Bridge.Functions.ScratchGrow

/-!
# `parse_str` (646) with escapes: the cost and the room of a run (M6)

The run `strRun` appends to the scratch twice per escape: the plain bytes before the `\` (613), then the
escape's bytes (649). Each append may grow the scratch, which changes its capacity, the free list's
bound and the memory's length (`ScratchGrow.capAfter`, `fAfter`, `hlAfter`).

* `costRun cfg F cap acc l L`: the cost of the run over `l` (the input from the reader's index, `L` the
  input's length), the scratch holding `acc` with capacity `cap` on `heapInv … F`. Per segment: the
  scan (30 per byte), `as_str`'s `cost927` on the bytes, the appends' `costExt` (with their growth),
  649's bound, and an error box at the end.
* `roomRun maxP hl cap acc l`: room under the memory limit for every growth and every error box the
  run may need, whichever way the memory grew before.
-/

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near
open WNear.Binary.ParseEscape (escDecode escK)
open NearInterface.Json (unicodeEscape)
open WNear.Binary.ScratchGrow (capAfter fAfter hlAfter roomRes costExt)
open WNear.Binary.SerdeErrBox (costErr roomFor4)
open WNear.Binary.FromUtf8 (cost927)

/-- 649's cost on the bytes `rest` after a `\`, the scratch holding `acc` (`ParseEscape.cost649`). -/
def costEsc (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc rest : List UInt8) (L : Nat) : Nat :=
  3000 * cfg.regularOpCost + 8 * costErr cfg F L +
    costExt cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (escK rest))

/-- The cost of `parse_str`'s run over `l`. -/
def costRun (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) : Nat :=
  let body := l.takeWhile plain
  let base := (500 + 30 * body.length + cost927 (acc.length + body.length)) * cfg.regularOpCost +
    costErr cfg (F + 2) (L + 1) + costExt cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)
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

/-- Room for the run's growths and error boxes, for every way the memory may have grown. -/
def roomRun (maxP hl : Nat) (cap : UInt32) (acc l : List UInt8) : Prop :=
  let body := l.takeWhile plain
  roomFor4 hl maxP 20 ∧ roomRes hl maxP cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) ∧
  ∀ hl1, hlAfter hl hl1 cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) →
    roomFor4 hl1 maxP 20 ∧
    match h : l.dropWhile plain with
    | x :: rest =>
      if x = 0x5C then
        let cap1 := capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)
        roomRes hl1 maxP cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat (escK rest)) ∧
        ∀ hl2, hlAfter hl1 hl2 cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat (escK rest)) →
          match he : escDecode rest with
          | some (out, m) =>
            roomRun maxP hl2 (capAfter cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length))
              (acc ++ body ++ out) (rest.drop m)
          | none => True
      else True
    | [] => True
termination_by l.length
decreasing_by
  have h1 := dropWhile_length_le l plain
  rw [h] at h1
  simp at h1
  simp only [List.length_drop]
  omega

/-- The base cost of one segment of the run. -/
def costBase (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) : Nat :=
  (500 + 30 * (l.takeWhile plain).length + cost927 (acc.length + (l.takeWhile plain).length)) * cfg.regularOpCost +
    costErr cfg (F + 2) (L + 1) +
    costExt cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)

theorem costRun_stop (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat)
    (h : ∀ rest, l.dropWhile plain ≠ 0x5C :: rest) :
    costRun cfg F cap acc l L = costBase cfg F cap acc l L := by
  rw [costRun]
  split
  · rfl
  · rename_i x rest hd
    have : x ≠ 0x5C := fun e => h rest (by rw [hd, e])
    simp only [this, ite_false]; rfl

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
    unfold costBase
    congr 1
    split <;> simp_all

theorem roomRun_unfold (maxP hl : Nat) (cap : UInt32) (acc l : List UInt8) :
    roomRun maxP hl cap acc l ↔
      (roomFor4 hl maxP 20 ∧ roomRes hl maxP cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) ∧
      ∀ hl1, hlAfter hl hl1 cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) →
        roomFor4 hl1 maxP 20 ∧
        ∀ rest, l.dropWhile plain = 0x5C :: rest →
          roomRes hl1 maxP (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
            (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat (escK rest)) ∧
          ∀ hl2, hlAfter hl1 hl2 (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
              (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat (escK rest)) →
            ∀ out m, escDecode rest = some (out, m) →
              roomRun maxP hl2
                (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                  (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat out.length))
                (acc ++ l.takeWhile plain ++ out) (rest.drop m)) := by
  rw [roomRun]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun hl1 hh1 => ⟨(h3 hl1 hh1).1, ?_⟩⟩
    intro rest hd
    have h4 := (h3 hl1 hh1).2
    split at h4
    · rename_i x rest' hd'
      rw [hd] at hd'
      simp only [List.cons.injEq] at hd'
      obtain ⟨rfl, rfl⟩ := hd'
      simp only [ite_true] at h4
      refine ⟨h4.1, fun hl2 hh2 out m he => ?_⟩
      have h5 := h4.2 hl2 hh2
      split at h5
      · rename_i out' m' he'
        rw [he] at he'; simp only [Option.some.injEq, Prod.mk.injEq] at he'
        obtain ⟨rfl, rfl⟩ := he'
        exact h5
      · rename_i he'; rw [he] at he'; simp at he'
    · rename_i hd'; rw [hd] at hd'; simp at hd'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun hl1 hh1 => ⟨(h3 hl1 hh1).1, ?_⟩⟩
    split
    · rename_i x rest hd
      split
      · rename_i hx
        subst hx
        refine ⟨((h3 hl1 hh1).2 rest hd).1, fun hl2 hh2 => ?_⟩
        split
        · rename_i out m he
          exact ((h3 hl1 hh1).2 rest hd).2 hl2 hh2 out m he
        · trivial
      · trivial
    · trivial

theorem escDecode_len (l out : List UInt8) (m : Nat) (h : escDecode l = some (out, m)) :
    1 ≤ out.length ∧ out.length ≤ m ∧ m ≤ l.length := by
  match l with
  | [] => simp [escDecode] at h
  | e :: rest =>
    simp only [escDecode] at h
    split_ifs at h <;> (try (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp))
    cases hu : unicodeEscape rest with
    | none => rw [hu] at h; simp at h
    | some p =>
      obtain ⟨c, r⟩ := p
      rw [hu] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hl, hr⟩ := ParseEscape.ue_suffix _ _ _ hu
      have hc := String.length_utf8EncodeChar c
      have := c.utf8Size_pos
      have := c.utf8Size_le_four
      simp only [List.length_cons]
      omega

end WNear.Binary.ParseStr
