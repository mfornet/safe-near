import Bridge.Functions.ParseStrEsc
import Bridge.Functions.StrGrowthTrace

/-!
# Successful string results retaining the scratch-growth trace

The copied result exposes the exact final capacity/free-list bound and an upper
bound on memory length. These facts were previously lost behind `resStr`'s
existentials. The suffix trace invariant composes them through the actual loop.
-/

namespace WNear.Binary.ParseStrSuccess

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.ParseStr
open WNear.Binary.ScratchGrow (sbuf capAfter fAfter hlAfter endState endFreeBound growthPages)
open WNear.Binary.SerdeRead (rd)

/-- The remainder of the trace predicts the same final state as the original trace. -/
def traceInv (F0 hl0 : Nat) (cap0 : UInt32) (l0 : List UInt8)
    (F hl : Nat) (cap : UInt32) (acc l : List UInt8) : Prop :=
  endFreeBound F cap (UInt32.ofNat acc.length) (appendChunks l acc) = endFreeBound F0 cap0 0 (appendChunks l0 []) ∧
  (endState cap (UInt32.ofNat acc.length) (appendChunks l acc)).1 = (endState cap0 0 (appendChunks l0 [])).1 ∧
  hl + growthPages cap (UInt32.ofNat acc.length) (appendChunks l acc) * 65536 ≤
    hl0 + growthPages cap0 0 (appendChunks l0 []) * 65536

/-- The invariant holds before the first append. -/
theorem traceInv_refl (F hl : Nat) (cap : UInt32) (l : List UInt8) :
    traceInv F hl cap l F hl cap [] l := ⟨rfl, rfl, le_rfl⟩

/-- A reserve either reuses memory or grows by at most the pages charged by its contract. -/
theorem hlAfter_pages (hl hl' : Nat) (cap len k : UInt32) (h : hlAfter hl hl' cap len k) :
    hl' ≤ hl + (if ScratchGrow.fits cap len k then 0 else
      (WNear.Binary.AllocNewCell.cellPages (WNear.Binary.AllocAlloc.wordsOf (capAfter cap len k)) 1).toNat) * 65536 := by
  unfold hlAfter at h
  by_cases hf : ScratchGrow.fits cap len k
  · simp only [if_pos hf] at h ⊢
    omega
  · simp only [if_neg hf, capAfter] at h ⊢
    unfold WNear.Binary.VecFromElem.grownLen at h
    omega

/-- Two appends at a successful escape preserve the predicted final state and memory bound. -/
theorem traceInv_escape (F0 hl0 : Nat) (cap0 : UInt32) (l0 : List UInt8)
    (F hl hl1 hl2 : Nat) (cap : UInt32) (acc l body tail out : List UInt8) (m : Nat)
    (hi : traceInv F0 hl0 cap0 l0 F hl cap acc l)
    (hb : l.takeWhile plain = body) (hd : l.dropWhile plain = 0x5C :: tail)
    (he : ParseEscape.escDecode tail = some (out, m))
    (hh1 : hlAfter hl hl1 cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length))
    (hh2 : hlAfter hl1 hl2 (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length))
      (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length)) :
    traceInv F0 hl0 cap0 l0
      (fAfter (fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length))
        (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length))
        (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length)) hl2
      (capAfter (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length))
        (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length))
      (acc ++ body ++ out) (tail.drop m) := by
  have h1 := hlAfter_pages hl hl1 cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) hh1
  have h2 := hlAfter_pages hl1 hl2 (capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length))
    (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat out.length) hh2
  have hab : UInt32.ofNat acc.length + UInt32.ofNat body.length = UInt32.ofNat (acc ++ body).length := by
    simp [List.length_append, UInt32.ofNat_add]
  have habe : UInt32.ofNat (acc ++ body).length + UInt32.ofNat out.length = UInt32.ofNat (acc ++ body ++ out).length := by
    simp [List.length_append, UInt32.ofNat_add, UInt32.add_assoc]
  unfold traceInv at hi ⊢
  rw [appendChunks_esc l acc tail out m hd he, hb] at hi
  simp only [endFreeBound, endState, growthPages] at hi
  rw [hab, habe] at hi
  refine ⟨hi.1, hi.2.1, ?_⟩
  have hm := hi.2.2
  simp only [Nat.add_mul] at hm
  omega

/-- The final plain append of a copied string exposes the initial trace's exact endpoint. -/
theorem traceInv_close (F0 hl0 : Nat) (cap0 : UInt32) (l0 : List UInt8)
    (F hl hl1 : Nat) (cap : UInt32) (acc l body tail : List UInt8)
    (hi : traceInv F0 hl0 cap0 l0 F hl cap acc l)
    (hb : l.takeWhile plain = body) (hd : l.dropWhile plain = 0x22 :: tail) (ha : acc ≠ [])
    (hh : hlAfter hl hl1 cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length)) :
    capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = (endState cap0 0 (appendChunks l0 [])).1 ∧
    fAfter F cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = endFreeBound F0 cap0 0 (appendChunks l0 []) ∧
    hl1 ≤ hl0 + growthPages cap0 0 (appendChunks l0 []) * 65536 := by
  have hh' := hlAfter_pages hl hl1 cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) hh
  unfold traceInv at hi
  rw [appendChunks_close l acc tail hd, if_neg ha, hb] at hi
  simp only [endFreeBound, endState, growthPages, Nat.add_zero] at hi
  exact ⟨hi.2.1, hi.1, by have hm := hi.2.2; omega⟩

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The original result with exact copied-buffer endpoint information and a memory-growth bound. -/
def resStrTraced (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (out de ptr sc ptrS capS : UInt32)
    (ob bs : List UInt8) (i : Nat) : IProp GF :=
  match strRun (bs.drop i) [] with
  | .ok bytes rest =>
    if Utf8.utf8Ok bytes = true then
      iprop(n ↦[i32][ out.toNat ] 0 ∗ rd n de ptr bs (bs.length - rest.length) ∗
        n ↦[i32][ out.toNat + 12 ] UInt32.ofNat bytes.length ∗
        if borrowed (bs.drop i) then
          iprop(n ↦[i32][ out.toNat + 4 ] 0 ∗ n ↦[i32][ out.toNat + 8 ] (ptr + UInt32.ofNat i) ∗
            n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗
            sbuf n maxP hl live F ptrS capS [])
        else
          iprop(∃ (p cap : UInt32) (hl' F' : Nat),
            ⌜hl ≤ hl' ∧ cap = (endState capS 0 (appendChunks (bs.drop i) [])).1 ∧
              F' = endFreeBound F capS 0 (appendChunks (bs.drop i) []) ∧
              hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop i) []) * 65536⌝ ∗
            n ↦[i32][ out.toNat + 4 ] 1 ∗ n ↦[i32][ out.toNat + 8 ] p ∗
            n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗
            n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat bytes.length ∗ sbuf n maxP hl' live F' p cap bytes))
    else errStr n maxP hl live out de ptr sc ob bs
  | _ => errStr n maxP hl live out de ptr sc ob bs

/-- Forgetting endpoint information gives the original parser result. -/
theorem resStrTraced_forget (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (out de ptr sc ptrS capS : UInt32) (ob bs : List UInt8) (i : Nat) :
    resStrTraced (GF := GF) n maxP hl live F out de ptr sc ptrS capS ob bs i ⊢
      resStr n maxP hl live F out de ptr sc ptrS capS ob bs i := by
  unfold resStrTraced resStr
  cases hr : strRun (bs.drop i) [] with
  | eof | ctrl | badEsc => simp only [hr]; iintro H; iexact H
  | ok bytes rest =>
    simp only [hr]
    by_cases hu : Utf8.utf8Ok bytes = true
    · simp only [if_pos hu]
      by_cases hb : borrowed (bs.drop i)
      · simp only [if_pos hb]; iintro H; iexact H
      · simp only [if_neg hb]
        iintro ⟨O0, Hr, O12, %p, %cap, %hl', %F', %h, O4, O8, S0, S4, S8, Hsb⟩
        iframe O0 Hr O12
        iexists p, cap, hl', F'
        iframe O4 O8 S0 S4 S8 Hsb
        ipureintro
        exact h.1
    · simp only [if_neg hu]; iintro H; iexact H

/-- Weaken a function postcondition without changing its precondition or cost. -/
theorem spec_post {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P : List Value → IProp GF} {K : List Value → Nat}
    {Q Q' : List Value → List Value → IProp GF} (hQ : ∀ args rs, Q args rs ⊢ Q' args rs) :
    MFunSpec cfg lim d type inst mi code Cg P K Q ⊢ MFunSpec cfg lim d type inst mi code Cg P K Q' := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R HP Hc
  iapply mwpInvoke_wand
  isplitl [HP Hc]
  · iapply H $$ %args %R HP Hc
  isplit
  · dsimp only
    iintro %rs ⟨Hc, HQ⟩
    iframe Hc
    iapply hQ args rs
    iexact HQ
  · iintro HT; iexact HT

end Resource
end WNear.Binary.ParseStrSuccess
