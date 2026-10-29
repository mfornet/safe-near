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

end WNear.Binary.ParseStr
