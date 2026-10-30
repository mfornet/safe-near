import Bridge.Functions.SerdeIgnMachineTrace
import Bridge.Functions.SerdeIgnPure

/-! # Future closing bytes bound the active depth of the complete ignored-value machine -/

namespace WNear.Binary.SerdeIgnProgress

open NearInterface.Json WNear.JsonFuel WNear.IgnoreModel
open WNear.Binary.SerdeIgnMachineTrace

/-- Successful execution consumes at least `needed` input bytes. -/
def Bound (needed input : Nat) (res : Option Result) : Prop :=
  ∀ r ops, res = some (r, ops) → r.length + needed ≤ input

theorem bound_none (needed input : Nat) : Bound needed input none := by
  intro r ops h; cases h

theorem bound_shift {needed input needed' input' : Nat} {res : Option Result}
    (h : Bound needed input res) (hle : needed' + input ≤ needed + input') : Bound needed' input' res := by
  intro r ops hr
  have := h r ops hr
  omega

theorem bound_mark (op : SerdeIgnTrace.Op) {needed input : Nat} {res : Option Result}
    (h : Bound needed input res) : Bound needed input (mark op res) := by
  intro r ops hr
  simp only [mark, Option.map_eq_some_iff] at hr
  obtain ⟨⟨r', ops'⟩, hres, he⟩ := hr
  cases he
  exact h r' ops' hres

theorem bound_saved (frames : List UInt8) {needed input : Nat} {res : Option Result}
    (h : Bound needed input res) : Bound needed input (save frames res) := by
  cases frames with
  | nil => exact h
  | cons f frames => exact bound_mark true h

/-- A pop leaves one byte to consume for each remaining represented frame. -/
theorem bound_pop (record : Bool) (frames r : List UInt8)
    (k : UInt8 → List UInt8 → List UInt8 → Option Result)
    (hk : ∀ f frames r, Bound (frames.length + 1) r.length (k f frames r)) :
    Bound frames.length r.length (pop record frames r k) := by
  cases frames with
  | nil =>
    intro r' ops h
    simp only [pop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons f frames =>
    cases record
    · simpa only [pop, Bool.false_eq_true, ite_false, List.length_cons] using hk f frames r
    · simpa only [pop, ite_true, List.length_cons] using bound_mark false (hk f frames r)

theorem bound_key (sk : List UInt8 → Option (List UInt8))
    (hsk : ∀ r r', sk r = some r' → r'.length ≤ r.length) (needed : Nat) (r : List UInt8)
    (k : List UInt8 → Option Result) (hk : ∀ r, Bound needed r.length (k r)) :
    Bound needed r.length (key sk r k) := by
  intro rest ops h
  unfold key at h
  split at h
  · rename_i r1 h1
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r2, h2, h⟩ := h
    split at h
    · rename_i r3 h3
      have hl1 := skip_cons_length h1
      have hl2 := hsk _ _ h2
      have hl3 := skip_cons_length h3
      exact bound_shift (hk r3) (by omega) rest ops h
    · cases h
  · cases h

/-- Every successful mode consumes a byte for its current work and each pending outer frame.
This is stronger than physical-vector legality: even the final unrecorded close is counted. -/
theorem run_bound (sv sk : List UInt8 → Option (List UInt8))
    (hsv : ∀ r r', sv r = some r' → r'.length < r.length)
    (hsk : ∀ r r', sk r = some r' → r'.length ≤ r.length)
    (n : Nat) (mode : Mode) (frames bs : List UInt8) :
    Bound (frames.length + 1) bs.length (run sv sk n mode frames bs) := by
  induction n generalizing mode frames bs with
  | zero => exact bound_none _ _
  | succ n ih =>
    cases mode with
    | val =>
      simp only [run]
      split
      · rename_i r hs
        have hl := skip_cons_length hs
        exact bound_shift (bound_saved frames (ih (.opened 0x5B) frames r)) (by omega)
      · rename_i r hs
        have hl := skip_cons_length hs
        exact bound_shift (bound_saved frames (ih (.opened 0x7B) frames r)) (by omega)
      · intro rest ops h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨r, hr, h⟩ := h
        have hl := hsv _ _ hr
        have hw := skip_length bs
        exact bound_shift (bound_pop false frames r (fun f frames r => run sv sk n (.cont f) frames r)
          (fun f frames r => ih (.cont f) frames r)) (by omega) rest ops h
    | opened f =>
      simp only [run]
      split
      · split
        · rename_i r hs
          have hl := skip_cons_length hs
          exact bound_shift (bound_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
        · apply bound_shift (ih .val (0x5B :: frames) (skipWhitespace bs))
          have hw := skip_length bs
          simp only [List.length_cons]
          omega
      · split
        · rename_i r hs
          have hl := skip_cons_length hs
          exact bound_shift (bound_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
        · have hw := skip_length bs
          apply bound_shift (bound_key sk hsk (frames.length + 1) (skipWhitespace bs) _ ?_) (by omega)
          intro r
          apply bound_shift (ih .val (0x7B :: frames) r)
          simp only [List.length_cons]
          omega
    | cont f =>
      simp only [run]
      split
      · rename_i r hs
        have hl := skip_cons_length hs
        split
        · apply bound_shift (ih .val (0x5B :: frames) r)
          simp only [List.length_cons]
          omega
        · apply bound_shift (bound_key sk hsk (frames.length + 1) r _ ?_) (by omega)
          intro r
          apply bound_shift (ih .val (0x7B :: frames) r)
          simp only [List.length_cons]
          omega
      · rename_i r hs
        have hl := skip_cons_length hs
        split
        · exact bound_shift (bound_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
        · exact bound_none _ _
      · rename_i r hs
        have hl := skip_cons_length hs
        split
        · exact bound_none _ _
        · exact bound_shift (bound_pop true frames r (fun g frames r => run sv sk n (.cont g) frames r)
            (fun g frames r => ih (.cont g) frames r)) (by omega)
      · exact bound_none _ _

/-- Full model success supplies enough future input to reserve work for every active frame. -/
theorem run_consumed (n : Nat) (mode : Mode) (frames bs r : List UInt8) (ops : List SerdeIgnTrace.Op)
    (h : run vSkip keyBody n mode frames bs = some (r, ops)) :
    r.length + frames.length + 1 ≤ bs.length := by
  have hb := run_bound vSkip keyBody (fun _ _ => IgnoreShallow.vSkip_strict) keyBody_length n mode frames bs
  have := hb r ops h
  omega

end WNear.Binary.SerdeIgnProgress
