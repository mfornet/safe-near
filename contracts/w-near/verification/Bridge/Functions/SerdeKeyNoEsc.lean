import Bridge.Functions.SerdeCost
import Bridge.Functions.ToVec

/-!
# `Hyp646` on an input without escapes (M6)

`SerdeStructObj.Hyp646` asks that `parse_str` (646) read every key `stringBody` decodes, the heap
unchanged. `SerdeNextKey.f646_key_noesc` proves it for one key whose body has no `\`. On an input
with no `\` byte at all, every key is such a key: its body is the plain bytes up to the closing quote
(`keyBody`), and the model's key is that body (`key_noesc`, through `ParseStr.noesc_model`).
`hyp646_noesc` is `Hyp646` on such an input, at the cost `K646` (`300 + 130` per byte read, from
`ParseStr.cost646`), so `Lin646` holds with `a646 = 300`, `b646 = 130` (`lin646_noesc`).
-/

namespace WNear.Binary.SerdeKeyNoEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeErrBox (errCode roomFor4)
open WNear.Binary.SerdeNextKey (Spec646)
open WNear.Binary.SerdeStructObj (Hyp646)
open WNear.Binary.ParseStr (plain ok646)
open NearInterface.Json

/-- A key's body at `q`: the plain bytes up to the first byte that is not. -/
def keyBody (bs : List UInt8) (q : Nat) : List UInt8 := (bs.drop q).takeWhile plain

/-- 646's cost on an escape-free key at `q` that it accepts. -/
def K646 (cfg : WasmConfig) (bs : List UInt8) (q : Nat) : Nat :=
  (330 + 30 * (keyBody bs q).length + FromUtf8.cost927 (keyBody bs q).length) * cfg.regularOpCost

theorem takeWhile_mem {p : UInt8 → Bool} {l : List UInt8} {b : UInt8} (h : b ∈ l.takeWhile p) : p b = true := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hy
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact hy
      · exact ih h
    · simp at h

theorem dropWhile_head {p : UInt8 → Bool} {l r : List UInt8} {x : UInt8} (h : l.dropWhile p = x :: r) :
    p x = false := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · rename_i hy
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simpa using hy

/-- **A key on an input without `\`**: the input at `q` is its body, the closing quote and the rest;
646 accepts it (`ok646`), and the key's UTF-8 bytes are the body. -/
theorem key_noesc {bs : List UInt8} (hnb : (0x5C : UInt8) ∉ bs) {q : Nat} {k : String} {rest1 : List UInt8}
    (hs : stringBody (bs.drop q) [] = some (some k, rest1)) :
    bs.drop q = keyBody bs q ++ (bs.drop q).dropWhile plain ∧ (∀ b ∈ keyBody bs q, plain b = true) ∧
      (∀ x rest, (bs.drop q).dropWhile plain = x :: rest → plain x = false ∧ x ≠ 0x5C) ∧
      ok646 (keyBody bs q) ((bs.drop q).dropWhile plain) ∧
      (bs.drop q).dropWhile plain = 0x22 :: rest1 ∧ k.toUTF8.toList = keyBody bs q := by
  have hsplit : bs.drop q = keyBody bs q ++ (bs.drop q).dropWhile plain := List.takeWhile_append_dropWhile.symm
  have hplain : ∀ b ∈ keyBody bs q, plain b = true := fun b hb => takeWhile_mem hb
  have hstop : ∀ x rest, (bs.drop q).dropWhile plain = x :: rest → plain x = false ∧ x ≠ 0x5C := by
    intro x rest h
    refine ⟨dropWhile_head h, ?_⟩
    intro e
    subst e
    apply hnb
    have hm : (0x5C : UInt8) ∈ (bs.drop q).dropWhile plain := by rw [h]; exact List.mem_cons_self
    exact List.mem_of_mem_drop ((List.dropWhile_sublist _).subset hm)
  have hm := ParseStr.noesc_model bs (keyBody bs q) ((bs.drop q).dropWhile plain) q hsplit hplain hstop
  by_cases hok : ok646 (keyBody bs q) ((bs.drop q).dropWhile plain)
  · rw [if_pos hok] at hm
    obtain ⟨s, rest, htl, hs', hb⟩ := hm
    rw [hs] at hs'
    simp only [Option.some.injEq, Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    refine ⟨hsplit, hplain, hstop, hok, htl, ?_⟩
    rw [String.toUTF8_eq_toByteArray, hb, ToVec.toList_eq, List.toList_data_toByteArray]
  · rw [if_neg hok] at hm
    exact absurd hs (hm k rest1)

/-- `Lin646` for `K646`: `300 + 130` per byte the key reads (its body and its closing quote). -/
theorem lin646_noesc (cfg : WasmConfig) (bs : List UInt8) (hnb : (0x5C : UInt8) ∉ bs) :
    SerdeCost.Lin646 cfg.regularOpCost (K646 cfg bs) bs 300 130 := by
  intro q k r hq hs
  obtain ⟨hsplit, -, -, -, htl, -⟩ := key_noesc hnb hs
  have hl := congrArg List.length hsplit
  rw [htl] at hl
  simp only [List.length_drop, List.length_append, List.length_cons] at hl
  unfold K646 FromUtf8.cost927
  apply Nat.mul_le_mul_right
  omega

section Hyp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`Hyp646` on an input without `\`**, at the cost `K646`, from `f646_key_noesc` at each key, for
any persistent `Cd` that holds 646's code. -/
theorem hyp646_noesc (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType) (de ptr idx : UInt32)
    (bs : List UInt8) (maxP : Nat) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hnb : (0x5C : UInt8) ∉ bs) (Cd : IProp GF) [Persistent Cd]
    (hCd : Cd ⊢ errCode n maxP inst mi A ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗
      A 657 ↪[wf] FuncInst.wasm types[31]! inst f657 ∗ A 647 ↪[wf] FuncInst.wasm types[31]! inst f647 ∗
      A 648 ↪[wf] FuncInst.wasm types[45]! inst f648) :
    Hyp646 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP (K646 cfg bs) Cd := by
  intro d sp ob q k rest1 mlen F live hd hob hsp hq hr hs
  obtain ⟨hsplit, hplain, hstop, hok, htl, hkb⟩ := key_noesc hnb hs
  have s := SerdeNextKey.f646_key_noesc (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt sp de ptr idx
    ob bs (keyBody bs q) ((bs.drop q).dropWhile plain) q maxP mlen live F hob hlen hptr hde hsp hq hsplit hplain
    hstop hok hr
  have hc : ParseStr.cost646 cfg F q (keyBody bs q) ((bs.drop q).dropWhile plain) = K646 cfg bs q := by
    unfold ParseStr.cost646 K646; rw [if_pos hok]; simp
  rw [hc] at s
  have hq' : bs.drop (q + (keyBody bs q).length + 1) = rest1 := by
    rw [← List.drop_drop, ← List.drop_drop, hsplit, htl, List.drop_left' rfl]; rfl
  have hql : q + (keyBody bs q).length + 1 ≤ bs.length := by
    have hl := congrArg List.length hsplit
    rw [htl] at hl
    simp only [List.length_drop, List.length_append, List.length_cons] at hl
    omega
  rw [hkb]
  iintro #HC
  ihave #H := hCd $$ HC
  ihave #S := s $$ H
  clear s
  iunfold Spec646 at S
  iunfold Spec646
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 (sp - 16), .i32 de, .i32 (de + 12)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
      stk n (sp.toNat - 176) 160 ∗ n ↦[wms][ (sp - 16).toNat ] ob ∗ rd n de ptr bs q ∗
      n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗ iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width)))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n (sp.toNat - 176) 160 ∗
      ∃ (t p : UInt32), ⌜p.toNat + (keyBody bs q).length ≤ 2 ^ 32 ∧ (keyBody bs q).length < 2 ^ 32⌝ ∗
        n ↦[i32][ (sp - 16).toNat ] 0 ∗ n ↦[i32][ (sp - 16).toNat + 4 ] t ∗
        n ↦[i32][ (sp - 16).toNat + 8 ] p ∗ n ↦[i32][ (sp - 16).toNat + 12 ] (UInt32.ofNat (keyBody bs q).length) ∗
        n ↦[wms][ p.toNat ] (keyBody bs q) ∗ (n ↦[wms][ p.toNat ] (keyBody bs q) -∗
          iprop(vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
            n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[i32][ (de + 12).toNat + 8 ] 0 ∗
            rd n de ptr bs (q + (keyBody bs q).length + 1))))) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hs, Ho, Hrd, Hsc, Hvt, Hh, He, Hw⟩
    iframe Hg Hs Ho Hrd Hsc Hvt Hh He Hw
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨-, %hrs, Hg, Hs, %t, %p, %hp, W0, W4, W8, W12, Hk, Hw⟩
    iframe Hg Hs
    isplitr
    · ipureintro; exact hrs
    iexists t
    iexists p
    isplitr
    · ipureintro; exact hp
    iframe W0 W4 W8 W12 Hk
    iintro Hk
    ihave HQ := Hw $$ Hk
    icases HQ with ⟨Hvt, Hh, He, Hu, Hsc, Hrd⟩
    iframe Hvt Hh He Hu Hsc
    iexists q + (keyBody bs q).length + 1
    iframe Hrd
    ipureintro; exact ⟨hq', hql⟩
  iexact S

end Hyp

end WNear.Binary.SerdeKeyNoEsc
