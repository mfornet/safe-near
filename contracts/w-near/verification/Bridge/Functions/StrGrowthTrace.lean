import Bridge.Functions.StrSuccessFitBound
import Bridge.Functions.ScratchGrowthTrace

/-!
# The successful string budget, with only real scratch-growth charges remaining

`appendChunks` follows the two appends at an escape and the last append of a
copied string. A borrowed string has no append. The cost theorem includes all
fitting work in the existing 470-ops-per-byte allowance and isolates only the
concrete growth trace, including its changing allocator bound.
-/

namespace WNear.Binary.ParseStrSuccess

open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseEscape (escDecode escK)
open WNear.Binary.ScratchGrow (fits capAfter fAfter extraStep extraCost)
open WNear.Binary.FromUtf8 (cost927)

/-- The append lengths charged on a successful run, excluding borrowed strings' nonexistent append. -/
def appendChunks (l acc : List UInt8) : List UInt32 :=
  match h : l.dropWhile plain with
  | [] => []
  | x :: tail =>
    if x = 0x5C then
      match he : escDecode tail with
      | some (out, m) => UInt32.ofNat (l.takeWhile plain).length :: UInt32.ofNat out.length ::
          appendChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out)
      | none => []
    else if acc = [] then [] else [UInt32.ofNat (l.takeWhile plain).length]
termination_by l.length
decreasing_by
  have ht := dropWhile_length_le l plain
  rw [h] at ht
  simp only [List.length_cons, List.length_drop] at *
  omega

/-- At a closing quote only a copied string appends its plain tail. -/
theorem appendChunks_close (l acc tail : List UInt8) (hd : l.dropWhile plain = 0x22 :: tail) :
    appendChunks l acc = if acc = [] then [] else [UInt32.ofNat (l.takeWhile plain).length] := by
  rw [appendChunks]
  split
  · rename_i hh; rw [hd] at hh; cases hh
  · rename_i x rest hh
    rw [hd] at hh
    simp only [List.cons.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp

/-- Every successful escape contributes its plain segment and its decoded bytes. -/
theorem appendChunks_esc (l acc tail out : List UInt8) (m : Nat)
    (hd : l.dropWhile plain = 0x5C :: tail) (he : escDecode tail = some (out, m)) :
    appendChunks l acc = UInt32.ofNat (l.takeWhile plain).length :: UInt32.ofNat out.length ::
      appendChunks (tail.drop m) (acc ++ l.takeWhile plain ++ out) := by
  rw [appendChunks]
  split
  · rename_i hh; rw [hd] at hh; cases hh
  · rename_i x rest hh
    rw [hd] at hh
    simp only [List.cons.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp only [ite_true]
    split <;> simp_all

/-- The encoded escape pays for all fitting work; only its actual growth reserve is separate. -/
theorem escape_growth_charge (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l out : List UInt8) (m : Nat)
    (he : escDecode l = some (out, m)) :
    (486 + 100 * out.length) * cfg.regularOpCost + ParseEscapeFast.cost649 cfg F cap acc l ≤
      470 * (m + 1) * cfg.regularOpCost +
        extraStep cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat out.length) := by
  have hw := escape_width l out m he
  have hk : escK l = out.length := by simp [escK, he]
  have hout : (UInt32.ofNat out.length).toNat = out.length := by simp; omega
  by_cases hu : l.head? = some 0x75
  · have hm := escape_unicode_length l out m hu he
    have hops := (ParseEscapeFast.workOps_le l).trans (ParseEscapeSuccessCost.successOps_le l out m he)
    have hmul := Nat.mul_le_mul_right cfg.regularOpCost hops
    have hmcpy : MemCpy.cost out.length ≤ 18 * out.length + 6 := by unfold MemCpy.cost; split <;> omega
    have hcp := Nat.mul_le_mul_right cfg.regularOpCost hmcpy
    have hbudget : 486 + 100 * out.length + 200 * (m + 1) + 260 + (18 * out.length + 6) ≤ 470 * (m + 1) := by omega
    have hb := Nat.mul_le_mul_right cfg.regularOpCost hbudget
    have hext := ScratchGrow.costExt_extra cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat out.length)
    unfold ParseEscapeFast.cost649 ParseEscapeFast.appendCost
    simp only [if_pos hu, hk]
    rw [hout] at hext
    simp only [Nat.add_mul] at hb hcp ⊢
    omega
  · obtain ⟨ho, hm⟩ := escape_simple_length l out m hu he
    have hpush := ScratchGrow.pushCost_extra cfg F cap (UInt32.ofNat acc.length)
    simp only [ParseEscapeFast.cost649, ParseEscapeFast.workOps, ParseEscapeFast.appendCost,
      if_neg hu, ho, hm, UInt32.ofNat_one]
    omega

/-- All accepting work, including fitting appends and final UTF-8, fits the 470-op budget.
Only the concrete allocating/growing reserve sequence remains to be amortized. -/
theorem costRun_growth (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l bytes rest : List UInt8) (L : Nat)
    (hok : strRun l acc = .ok bytes rest) (hsmall : acc.length + l.length < 2 ^ 27) :
    rest.length < l.length ∧ costRun cfg F cap acc l L ≤
      (400 + 470 * (l.length - rest.length) + 100 * acc.length) * cfg.regularOpCost +
        extraCost cfg F cap (UInt32.ofNat acc.length) (appendChunks l acc) := by
  induction hn : l.length using Nat.strong_induction_on generalizing F cap acc l bytes rest with
  | _ len ih =>
    rw [← hn]
    have hsplit := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
    simp only [List.length_append] at hsplit
    have hb : (l.takeWhile plain).length ≤ l.length := by omega
    have hb32 : (UInt32.ofNat (l.takeWhile plain).length).toNat = (l.takeWhile plain).length := by simp; omega
    have hmc : MemCpy.cost (l.takeWhile plain).length ≤ 18 * (l.takeWhile plain).length + 6 := by
      unfold MemCpy.cost; split <;> omega
    have hext := ScratchGrow.extCost_extra cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)
    rw [hb32] at hext
    cases hd : l.dropWhile plain with
    | nil => rw [strRun_nil _ _ hd] at hok; cases hok
    | cons x tail =>
      have hl : l.length = (l.takeWhile plain).length + 1 + tail.length := by
        rw [hd] at hsplit
        simp only [List.length_cons] at hsplit
        omega
      rw [strRun_cons _ _ x tail hd] at hok
      by_cases h22 : x = 0x22
      · subst x
        simp only [ite_true, StrOut.ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨by omega, ?_⟩
        have hno : ∀ r, l.dropWhile plain ≠ 0x5C :: r := by intro r; rw [hd]; simp
        rw [costRun_stop cfg F cap acc l L hno, costBase_close cfg F cap acc l tail L hd,
          appendChunks_close l acc tail hd]
        have hop : 300 + 30 * (l.takeWhile plain).length + cost927 (acc.length + (l.takeWhile plain).length) +
            180 + MemCpy.cost (l.takeWhile plain).length ≤ 400 + 470 * (l.length - tail.length) + 100 * acc.length := by
          unfold cost927
          omega
        have hm := Nat.mul_le_mul_right cfg.regularOpCost hop
        by_cases ha : acc = []
        · simp only [if_pos ha, extraCost, Nat.add_zero]
          simp only [Nat.add_mul] at hm ⊢
          omega
        · simp only [if_neg ha, extraCost, Nat.add_zero]
          simp only [Nat.add_mul] at hm ⊢
          omega
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
            have hnew : (acc ++ l.takeWhile plain ++ eo).length + (tail.drop m).length ≤ acc.length + l.length := by
              simp only [List.length_append, List.length_drop]
              omega
            have hrec := ih (tail.drop m).length (by simp; omega)
              (fAfter (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length))
              (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length))
              (acc ++ l.takeWhile plain ++ eo) (tail.drop m) bytes rest hok (by omega) rfl
            refine ⟨by have := hrec.1; simp only [List.length_drop] at this; omega, ?_⟩
            rw [costRun_esc cfg F cap acc l tail L hd, costBase_esc cfg F cap acc l tail L hd, he,
              appendChunks_esc l acc tail eo m hd he, extraCost, extraCost]
            have hab : UInt32.ofNat acc.length + UInt32.ofNat (l.takeWhile plain).length =
                UInt32.ofNat (acc ++ l.takeWhile plain).length := by simp [List.length_append, UInt32.ofNat_add, UInt32.add_assoc]
            rw [hab]
            have habe : UInt32.ofNat (acc ++ l.takeWhile plain).length + UInt32.ofNat eo.length =
                UInt32.ofNat (acc ++ l.takeWhile plain ++ eo).length := by simp [List.length_append, UInt32.ofNat_add, UInt32.add_assoc]
            rw [habe]
            unfold costEsc
            have hesc := escape_growth_charge cfg
              (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
              (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
              (acc ++ l.takeWhile plain) tail eo m he
            have hmc' := Nat.mul_le_mul_right cfg.regularOpCost hmc
            have hcons : l.length - rest.length = (l.takeWhile plain).length + (m + 1) + ((tail.drop m).length - rest.length) := by
              have := hrec.1
              simp only [List.length_drop] at this ⊢
              omega
            rw [hcons]
            have hrec' := hrec.2
            have hbody : (30 * (l.takeWhile plain).length + 18 * (l.takeWhile plain).length +
                100 * (l.takeWhile plain).length) * cfg.regularOpCost ≤
                470 * (l.takeWhile plain).length * cfg.regularOpCost := Nat.mul_le_mul_right cfg.regularOpCost (by omega)
            simp only [Nat.add_mul] at hbody
            simp only [List.length_append, Nat.add_mul, Nat.mul_add, ← Nat.mul_assoc] at hrec' hesc hmc' ⊢
            omega
        · simp [h92] at hok

/-- An admissible reserve keeps the used length inside its capacity and the capacity below 2^28. -/
theorem reserve_state (cap len k : UInt32) (hused : len.toNat ≤ cap.toNat)
    (hc : cap.toNat < 2 ^ 28) (hsmall : len.toNat + k.toNat < 2 ^ 27) :
    (len + k).toNat ≤ (capAfter cap len k).toNat ∧ (capAfter cap len k).toNat < 2 ^ 28 := by
  have hs : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
  unfold capAfter
  split
  · rename_i hf
    simp only [fits] at hf
    rw [hs]
    omega
  · rename_i hf
    simp only [fits] at hf
    rw [VecGrow.growCap_toNat cap (len + k) (by omega), hs]
    omega

/-- The successful run's actual append sequence satisfies the reserve contracts' arithmetic bounds.
The final scratch length is at most the decoded string length (a borrowed string leaves scratch empty). -/
theorem appendChunks_valid (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest) (hacc : acc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 28) (hsmall : acc.length + l.length < 2 ^ 27) :
    ScratchGrow.validTrace cap (UInt32.ofNat acc.length) (appendChunks l acc) ∧
      (ScratchGrow.endState cap (UInt32.ofNat acc.length) (appendChunks l acc)).2.toNat ≤ bytes.length ∧
      (ScratchGrow.endState cap (UInt32.ofNat acc.length) (appendChunks l acc)).1.toNat < 2 ^ 28 := by
  induction hn : l.length using Nat.strong_induction_on generalizing cap acc l bytes rest with
  | _ len ih =>
    have hsplit := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
    simp only [List.length_append] at hsplit
    have hb : (l.takeWhile plain).length ≤ l.length := by omega
    have ha32 : (UInt32.ofNat acc.length).toNat = acc.length := by simp; omega
    have hb32 : (UInt32.ofNat (l.takeWhile plain).length).toNat = (l.takeWhile plain).length := by simp; omega
    have hab : UInt32.ofNat acc.length + UInt32.ofNat (l.takeWhile plain).length =
        UInt32.ofNat (acc ++ l.takeWhile plain).length := by simp [List.length_append, UInt32.ofNat_add]
    have hab32 : (UInt32.ofNat (acc ++ l.takeWhile plain).length).toNat = (acc ++ l.takeWhile plain).length := by
      simp only [List.length_append]
      simp; omega
    have hw1 := reserve_state cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length)
      (by rw [ha32]; exact hacc) hcap (by rw [ha32, hb32]; omega)
    rw [hab, hab32] at hw1
    cases hd : l.dropWhile plain with
    | nil => rw [strRun_nil _ _ hd] at hok; cases hok
    | cons x tail =>
      have hl : l.length = (l.takeWhile plain).length + 1 + tail.length := by
        rw [hd] at hsplit
        simp only [List.length_cons] at hsplit
        omega
      rw [strRun_cons _ _ x tail hd] at hok
      by_cases h22 : x = 0x22
      · subst x
        simp only [ite_true, StrOut.ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        rw [appendChunks_close l acc tail hd]
        by_cases ha : acc = []
        · simpa [ha, ScratchGrow.validTrace, ScratchGrow.endState] using hcap
        · simp only [if_neg ha, ScratchGrow.validTrace, ScratchGrow.endState, hab, hab32]
          exact ⟨⟨by rw [ha32]; exact hacc, by omega, by rw [ha32, hb32]; omega, trivial⟩, le_rfl, hw1.2⟩
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
            have hnew : (acc ++ l.takeWhile plain ++ eo).length + (tail.drop m).length ≤ acc.length + l.length := by
              simp only [List.length_append, List.length_drop]
              omega
            have heo32 : (UInt32.ofNat eo.length).toNat = eo.length := by simp; omega
            have habe : UInt32.ofNat (acc ++ l.takeWhile plain).length + UInt32.ofNat eo.length =
                UInt32.ofNat (acc ++ l.takeWhile plain ++ eo).length := by
              simp [List.length_append, UInt32.ofNat_add, UInt32.add_assoc]
            have habe32 : (UInt32.ofNat (acc ++ l.takeWhile plain ++ eo).length).toNat =
                (acc ++ l.takeWhile plain ++ eo).length := by
              simp only [List.length_append]
              simp; omega
            have hw2 := reserve_state (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
              (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length)
              (by rw [hab32]; exact hw1.1) hw1.2 (by rw [hab32, heo32]; simp only [List.length_append]; omega)
            rw [habe, habe32] at hw2
            have hr := ih (tail.drop m).length (by simp; omega)
              (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length))
                (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length))
              (acc ++ l.takeWhile plain ++ eo) (tail.drop m) bytes rest hok hw2.1 hw2.2 (by omega) rfl
            rw [appendChunks_esc l acc tail eo m hd he]
            simp only [ScratchGrow.validTrace, ScratchGrow.endState]
            rw [hab, habe]
            exact ⟨⟨by rw [ha32]; exact hacc, by omega, by rw [ha32, hb32]; omega,
              by rw [hab32]; exact hw1.1, by have := hw1.2; omega,
              by rw [hab32, heo32]; simp only [List.length_append]; omega, hr.1⟩, hr.2⟩
        · simp [h92] at hok

/-- All new scratch capacities requested by a successful string run are linear in decoded bytes. -/
theorem appendChunks_allocated (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest) (hacc : acc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 28) (hsmall : acc.length + l.length < 2 ^ 27) :
    ScratchGrow.allocatedBytes cap (UInt32.ofNat acc.length) (appendChunks l acc) ≤ 4 * bytes.length + 16 := by
  have hv := appendChunks_valid cap acc l bytes rest hok hacc hcap hsmall
  have ha := ScratchGrow.allocatedBytes_linear cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1
  have hl := hv.2.1
  omega

/-- The previous amortized copy theorem now applies to this parser's concrete append sequence. -/
theorem appendChunks_copyOps (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest) (hacc : acc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 28) (hsmall : acc.length + l.length < 2 ^ 27) :
    ScratchGrow.copyOps cap (UInt32.ofNat acc.length) (appendChunks l acc) ≤ 48 * bytes.length + 192 := by
  have hv := appendChunks_valid cap acc l bytes rest hok hacc hcap hsmall
  have hc := ScratchGrow.copyOps_linear cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1
  have hl := hv.2.1
  omega

/-- The allocator's page fees on this trace have a decoded-length and growth-count bound. -/
theorem appendChunks_pages (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest) (hacc : acc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 28) (hsmall : acc.length + l.length < 2 ^ 27) :
    ScratchGrow.growthPages cap (UInt32.ofNat acc.length) (appendChunks l acc) ≤
      (4 * bytes.length + 16 + 66066 * ScratchGrow.growthCount cap (UInt32.ofNat acc.length) (appendChunks l acc)) / 65536 := by
  have hv := appendChunks_valid cap acc l bytes rest hok hacc hcap hsmall
  have hp := ScratchGrow.growthPages_scaled cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1 hv.2.2
  have ha := appendChunks_allocated cap acc l bytes rest hok hacc hcap hsmall
  omega

/-- A trace with no growth has no residual growth charge, even when the string is large. -/
theorem extraCost_zero (cfg : WasmConfig) (F : Nat) (cap len : UInt32) (ks : List UInt32)
    (hz : ScratchGrow.growthCount cap len ks = 0) : extraCost cfg F cap len ks = 0 := by
  induction ks generalizing F cap len with
  | nil => rfl
  | cons k ks ih =>
    by_cases hf : fits cap len k
    · have ht : ScratchGrow.growthCount (capAfter cap len k) (len + k) ks = 0 := by
        simpa only [ScratchGrow.growthCount, if_pos hf, Nat.zero_add] using hz
      simp only [extraCost, ScratchGrow.extraStep, if_pos hf, Nat.zero_add]
      exact ih (fAfter F cap len k) (capAfter cap len k) (len + k) ht
    · simp [ScratchGrow.growthCount, hf] at hz

/-- A closed bound on the remaining trace charge. `F` is the initial allocator bound,
`G` the number of growths, and `N` the decoded byte length. No-growth traces cost zero. -/
def growthBudget (cfg : WasmConfig) (F G N : Nat) : Nat :=
  if G = 0 then 0 else
    (1790 * G + (F * G + G * G - G) * 320 + 36 * N + 144) * cfg.regularOpCost +
      G * cfg.linearOpBaseCost + cfg.linearOpUnitCost * ((4 * N + 16 + 66066 * G) / 65536)

/-- All allocator walks, reallocation copies and memory-growth fees of the actual string trace. -/
theorem appendChunks_growthBudget (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest) (hacc : acc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 28) (hsmall : acc.length + l.length < 2 ^ 27) :
    extraCost cfg F cap (UInt32.ofNat acc.length) (appendChunks l acc) ≤
      growthBudget cfg F (ScratchGrow.growthCount cap (UInt32.ofNat acc.length) (appendChunks l acc)) bytes.length := by
  have hv := appendChunks_valid cap acc l bytes rest hok hacc hcap hsmall
  have hg := ScratchGrow.extraCost_le cfg F cap (UInt32.ofNat acc.length) (appendChunks l acc)
  have hw := ScratchGrow.walkBounds_eq F cap (UInt32.ofNat acc.length) (appendChunks l acc)
  have hm := ScratchGrow.movedBytes_linear cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1
  have hlen := hv.2.1
  have hp := appendChunks_pages cap acc l bytes rest hok hacc hcap hsmall
  generalize hG : ScratchGrow.growthCount cap (UInt32.ofNat acc.length) (appendChunks l acc) = G at hg hw hp ⊢
  by_cases hz : G = 0
  · simp only [growthBudget, hz, ite_true]
    have he := extraCost_zero cfg F cap (UInt32.ofNat acc.length) (appendChunks l acc) (by omega)
    omega
  · simp only [growthBudget, if_neg hz]
    have hwalk : ScratchGrow.walkBounds F cap (UInt32.ofNat acc.length) (appendChunks l acc) = F * G + G * G - G := by omega
    rw [hwalk] at hg
    have hops : 1790 * G + (F * G + G * G - G) * 320 +
          18 * ScratchGrow.movedBytes cap (UInt32.ofNat acc.length) (appendChunks l acc) ≤
        1790 * G + (F * G + G * G - G) * 320 + 36 * bytes.length + 144 := by omega
    have hop := Nat.mul_le_mul_right cfg.regularOpCost hops
    have hpage := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
    omega

/-- The growth count is logarithmic in decoded length, including the initial allocation.
This power certificate avoids rounding conventions for logarithms. -/
theorem appendChunks_growthCount (cap : UInt32) (acc l bytes rest : List UInt8)
    (hok : strRun l acc = .ok bytes rest) (hacc : acc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 28) (hsmall : acc.length + l.length < 2 ^ 27) :
    let G := ScratchGrow.growthCount cap (UInt32.ofNat acc.length) (appendChunks l acc)
    G = 0 ∨ 8 * 2 ^ (G - 1) ≤ 2 * bytes.length + 8 := by
  dsimp only
  have hv := appendChunks_valid cap acc l bytes rest hok hacc hcap hsmall
  by_cases hz : ScratchGrow.growthCount cap (UInt32.ofNat acc.length) (appendChunks l acc) = 0
  · exact Or.inl hz
  · right
    have hp := ScratchGrow.growthCount_power cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1 (by omega)
    have hs := ScratchGrow.end_capacity_strict cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1 (by omega)
    have hc := ScratchGrow.endState_capacity cap (UInt32.ofNat acc.length) (appendChunks l acc) hv.1
    have hl := hv.2.1
    omega

end WNear.Binary.ParseStrSuccess
