import Bridge.Functions.SerdeBundledWork

namespace WNear.Binary.SerdeKeyReuse
open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseEscape (escDecode)
open WNear.Binary.ParseStrSuccess

/-- A successful copied string consumes an escape and its final quote. -/
theorem copied_consumed (cfg : WasmConfig) (l bytes rest : List UInt8)
    (hlen : l.length < 2 ^ 24) (hok : strRun l [] = .ok bytes rest) (hb : ¬ borrowed l) :
    3 ≤ l.length - rest.length := by
  have hsplit := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
  simp only [List.length_append] at hsplit
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
      exact False.elim (hb (by simp [borrowed, hd]))
    · simp only [if_neg h22] at hok
      by_cases h92 : x = 0x5C
      · subst x
        simp only [ite_true] at hok
        cases he : escDecode tail with
        | none => simp [he] at hok
        | some pair =>
          obtain ⟨out, m⟩ := pair
          simp only [he, List.nil_append] at hok
          have hcons := escDecode_len tail out m he
          have hm : 1 ≤ m := by
            by_cases hu : tail.head? = some 0x75
            · have hh := escape_unicode_length tail out m hu he; omega
            · have hh := escape_simple_length tail out m hu he; omega
          have hsmall : (l.takeWhile plain ++ out).length + (tail.drop m).length < 2 ^ 27 := by
            simp only [List.length_append, List.length_drop]
            omega
          have hrec := (costRun_growth_tight cfg 0 0 (l.takeWhile plain ++ out) (tail.drop m) bytes rest 0 hok hsmall).1
          simp only [List.length_drop] at hrec
          omega
      · simp [h92] at hok

theorem bundledCost_borrowed_tight (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (q : Nat) (key : String) (rest : List UInt8)
    (hb : borrowed (bs.drop q)) (hok : strRun (bs.drop q) [] = .ok key.toUTF8.toList rest)
    (hu : Utf8.utf8Ok key.toUTF8.toList = true) :
    SerdeKey.cost194 * cfg.regularOpCost + bundledCost cfg F cap bs key.toUTF8.toList rest q ≤
      ((if key.toUTF8.toList.length = 10 then 642 else 380) + 130 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost := by
  have he := keyCost_borrowed cfg F cap bs key.toUTF8.toList rest q hb hok hu
  simp only [keyCost, if_pos hb] at he
  have hraw : preciseCost cfg F cap bs key.toUTF8.toList rest q =
      (300 + 130 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost := by
    simpa only [preciseCost, if_pos hb] using he
  have hc : SerdeKey.cost194 = 342 := by decide
  have hbase : SerdeKey.cost194 ≤ 300 + 130 * ((bs.drop q).length - rest.length) + SerdeKeyTight.fieldCost key.toUTF8.toList := by
    rw [hc]
    unfold SerdeKeyTight.fieldCost
    split <;> omega
  have hbase' := Nat.mul_le_mul_right cfg.regularOpCost hbase
  unfold bundledCost
  rw [hraw]
  by_cases hk : key.toUTF8.toList.length = 10
  · simp only [SerdeKeyTight.fieldCost, if_pos hk, hc, Nat.add_mul] at hbase' ⊢
    omega
  · simp only [SerdeKeyTight.fieldCost, if_neg hk, hc, Nat.add_mul] at hbase' ⊢
    omega

/-- Distinguishing borrowed work from the shortest possible copied key improves the full member rate to 470. -/
theorem ignored_member_regular_budget_470 (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (q : Nat) (key : String) (rest : List UInt8) (m : Nat)
    (hlen : bs.length < 2 ^ 24) (hm : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    (942 + 166 + 470 * m) * cfg.regularOpCost + SerdeKey.cost194 * cfg.regularOpCost +
      bundledCost cfg F cap bs key.toUTF8.toList rest q ≤
    470 * (((bs.drop q).length - rest.length) + m + 3) * cfg.regularOpCost +
      ScratchGrow.extraCost cfg F cap 0 (appendChunks (bs.drop q) []) := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hm
  have hs := SerdeDeStrEsc.strRun_size (bs.drop q) [] key.toUTF8.toList rest hok
  simp only [List.length_nil, Nat.zero_add] at hs
  by_cases hb : borrowed (bs.drop q)
  · have hkey := bundledCost_borrowed_tight cfg F cap bs q key rest hb hok hu
    have hops : 942 + 166 + 470 * m + (if key.toUTF8.toList.length = 10 then 642 else 380) +
        130 * ((bs.drop q).length - rest.length) ≤ 470 * (((bs.drop q).length - rest.length) + m + 3) := by
      split <;> omega
    have hmul := Nat.mul_le_mul_right cfg.regularOpCost hops
    simp only [Nat.add_mul, Nat.mul_assoc] at hkey hmul ⊢
    omega
  · have hmin := copied_consumed cfg (bs.drop q) key.toUTF8.toList rest (by simp only [List.length_drop]; omega) hok hb
    have hkey := bundledCost_growth_tight cfg F cap bs q key rest hlen hm
    have hops : 942 + 166 + 470 * m + (if key.toUTF8.toList.length = 10 then 642 else 380) +
        433 * ((bs.drop q).length - rest.length) ≤ 470 * (((bs.drop q).length - rest.length) + m + 3) := by
      split <;> omega
    have hmul := Nat.mul_le_mul_right cfg.regularOpCost hops
    simp only [Nat.add_mul, Nat.mul_assoc] at hkey hmul ⊢
    omega

end WNear.Binary.SerdeKeyReuse
