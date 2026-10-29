import Bridge.Functions.StrSuccessCost

/-! # The accepting string allowance when its scratch already has capacity -/

namespace WNear.Binary.ParseStrSuccess

open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseEscape (escDecode escK)
open WNear.Binary.ScratchGrow (fits capAfter fAfter costExt costApp costRes)
open WNear.Binary.FromUtf8 (cost927)

/-- A successful escape emits at most four UTF-8 bytes. -/
theorem escape_width (l out : List UInt8) (m : Nat) (he : escDecode l = some (out, m)) : out.length ≤ 4 := by
  cases l with
  | nil => simp [escDecode] at he
  | cons e tail =>
    simp only [escDecode] at he
    split_ifs at he <;> (try (simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp))
    cases hu : NearInterface.Json.unicodeEscape tail with
    | none => simp [hu] at he
    | some p =>
      obtain ⟨c, rest⟩ := p
      rw [hu] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [String.length_utf8EncodeChar]
      exact c.utf8Size_le_four

/-- Every successful simple escape consumes and emits exactly one byte after the backslash. -/
theorem escape_simple_length (l out : List UInt8) (m : Nat)
    (hn : l.head? ≠ some 0x75) (he : escDecode l = some (out, m)) : out.length = 1 ∧ m = 1 := by
  cases l with
  | nil => simp [escDecode] at he
  | cons e tail =>
    have heu : e ≠ 0x75 := by simpa using hn
    simp only [escDecode] at he
    split_ifs at he <;> (try (simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp))
    all_goals simp_all

/-- A successful Unicode escape consumes at least its `u` and four hex digits. -/
theorem escape_unicode_length (l out : List UInt8) (m : Nat)
    (hu : l.head? = some 0x75) (he : escDecode l = some (out, m)) : 5 ≤ m := by
  cases l with
  | nil => simp at hu
  | cons e tail =>
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst e
    change (NearInterface.Json.unicodeEscape tail).map
      (fun p => (String.utf8EncodeChar p.1, 1 + (tail.length - p.2.length))) = some (out, m) at he
    obtain ⟨⟨c, rest⟩, hue, hp⟩ := Option.map_eq_some_iff.mp he
    have hm := congrArg Prod.snd hp
    have hs := ParseEscape.ue_suffix tail rest c hue
    simp only [Prod.snd] at hm
    omega

/-- The fixed overhead and emitted-byte validation fit the encoded escape's budget, including its append. -/
theorem escape_fit_charge (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l out : List UInt8) (m : Nat)
    (he : escDecode l = some (out, m))
    (hf : fits cap (UInt32.ofNat acc.length) (UInt32.ofNat out.length)) :
    (486 + 100 * out.length) * cfg.regularOpCost + ParseEscapeFast.cost649 cfg F cap acc l ≤
      470 * (m + 1) * cfg.regularOpCost := by
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
    unfold ParseEscapeFast.cost649 ParseEscapeFast.appendCost costExt costApp costRes
    simp only [if_pos hu, hk, if_pos hf, Nat.add_zero, hout]
    simp only [Nat.add_mul] at hb hcp ⊢
    omega
  · obtain ⟨ho, hm⟩ := escape_simple_length l out m hu he
    have hf1 : fits cap (UInt32.ofNat acc.length) 1 := by simpa only [ho, UInt32.ofNat_one] using hf
    simp only [ParseEscapeFast.cost649, ParseEscapeFast.workOps, ParseEscapeFast.appendCost,
      if_neg hu, ScratchFast.pushCost, if_pos hf1, ho, hm]
    omega

/-- The full accepting cost fits 470 ops per consumed encoded byte when the scratch needs no growth. -/
theorem costRun_fit (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l bytes rest : List UInt8) (L : Nat)
    (hok : strRun l acc = .ok bytes rest) (hroom : acc.length + l.length ≤ cap.toNat)
    (hsmall : acc.length + l.length < 2 ^ 27) :
    rest.length < l.length ∧ costRun cfg F cap acc l L ≤
      (400 + 470 * (l.length - rest.length) + 100 * acc.length) * cfg.regularOpCost := by
  induction hn : l.length using Nat.strong_induction_on generalizing F cap acc l bytes rest with
  | _ len ih =>
    rw [← hn]
    have hsplit := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
    simp only [List.length_append] at hsplit
    have hb : (l.takeWhile plain).length ≤ l.length := by omega
    have ha32 : (UInt32.ofNat acc.length).toNat = acc.length := by simp; omega
    have hb32 : (UInt32.ofNat (l.takeWhile plain).length).toNat = (l.takeWhile plain).length := by simp; omega
    have hfit : fits cap (UInt32.ofNat acc.length) (UInt32.ofNat (l.takeWhile plain).length) := by
      simp only [fits, ha32, hb32]
      omega
    have hmc : MemCpy.cost (l.takeWhile plain).length ≤ 18 * (l.takeWhile plain).length + 6 := by
      unfold MemCpy.cost; split <;> omega
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
        rw [costRun_stop cfg F cap acc l L hno, costBase_close cfg F cap acc l tail L hd]
        simp only [ScratchFast.extCost, if_pos hfit, hb32]
        have hop : 300 + 30 * (l.takeWhile plain).length + cost927 (acc.length + (l.takeWhile plain).length) +
            180 + MemCpy.cost (l.takeWhile plain).length ≤ 400 + 470 * (l.length - tail.length) + 100 * acc.length := by
          unfold cost927
          omega
        have hm := Nat.mul_le_mul_right cfg.regularOpCost hop
        simpa only [Nat.add_mul, Nat.add_assoc] using hm
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
            have hab32 : (UInt32.ofNat (acc ++ l.takeWhile plain).length).toNat = (acc ++ l.takeWhile plain).length := by
              simp only [List.length_append]
              simp; omega
            simp only [List.length_append] at hab32
            have heo32 : (UInt32.ofNat eo.length).toNat = eo.length := by simp; omega
            have hf2 : fits cap (UInt32.ofNat (acc ++ l.takeWhile plain).length) (UInt32.ofNat eo.length) := by
              simp only [fits, hab32, heo32, List.length_append]
              omega
            have hrec := ih (tail.drop m).length (by simp; omega) F cap
              (acc ++ l.takeWhile plain ++ eo) (tail.drop m) bytes rest hok (by omega) (by omega) rfl
            refine ⟨by have := hrec.1; simp only [List.length_drop] at this; omega, ?_⟩
            rw [costRun_esc cfg F cap acc l tail L hd, costBase_esc cfg F cap acc l tail L hd, he]
            simp only [capAfter, fAfter, if_pos hfit, if_pos hf2, ScratchFast.extCost, hb32]
            unfold costEsc
            have hesc := escape_fit_charge cfg F cap (acc ++ l.takeWhile plain) tail eo m he hf2
            have hmc' := Nat.mul_le_mul_right cfg.regularOpCost hmc
            have hcons : l.length - rest.length = (l.takeWhile plain).length + (m + 1) + ((tail.drop m).length - rest.length) := by
              have := hrec.1
              simp only [List.length_drop] at this ⊢
              omega
            rw [hcons]
            have hrec' := hrec.2
            have hbody : (30 * (l.takeWhile plain).length + 18 * (l.takeWhile plain).length +
                100 * (l.takeWhile plain).length) * cfg.regularOpCost ≤
                470 * (l.takeWhile plain).length * cfg.regularOpCost :=
              Nat.mul_le_mul_right cfg.regularOpCost (by omega)
            simp only [Nat.add_mul] at hbody
            simp only [List.length_append, Nat.add_mul, Nat.mul_add, ← Nat.mul_assoc] at hrec' hesc hmc' ⊢
            omega
        · simp [h92] at hok

end WNear.Binary.ParseStrSuccess
