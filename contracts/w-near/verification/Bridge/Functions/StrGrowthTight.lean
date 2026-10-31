import Bridge.Functions.StrGrowthSharp

set_option maxRecDepth 100000

namespace WNear.Binary.ParseStrSuccess
open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseEscape (escDecode escK)
open WNear.Binary.ScratchGrow (fits capAfter fAfter extraStep extraCost)
open WNear.Binary.FromUtf8 (cost927)

set_option maxRecDepth 100000
theorem costRun_growth_tight (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l bytes rest : List UInt8) (L : Nat)
    (hok : strRun l acc = .ok bytes rest) (hsmall : acc.length + l.length < 2 ^ 27) :
    rest.length < l.length ∧ costRun cfg F cap acc l L ≤
      (200 + 433 * (l.length - rest.length) + 100 * acc.length) * cfg.regularOpCost +
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
            180 + MemCpy.cost (l.takeWhile plain).length ≤ 200 + 433 * (l.length - tail.length) + 100 * acc.length := by
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
            have hesc := escape_growth_charge_sharp cfg
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
                433 * (l.takeWhile plain).length * cfg.regularOpCost := Nat.mul_le_mul_right cfg.regularOpCost (by omega)
            simp only [Nat.add_mul] at hbody
            simp only [List.length_append, Nat.add_mul, Nat.mul_add, ← Nat.mul_assoc] at hrec' hesc hmc' ⊢
            omega
        · simp [h92] at hok


end WNear.Binary.ParseStrSuccess
