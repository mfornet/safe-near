import Bridge.Functions.SerdeAccountIdEsc
import Bridge.Functions.SerdeSeqElem

/-!
# Changing scratch state at the struct's value-reader boundary

The account-id allocation and parser scratch are separate live blocks. This
boundary retains both and the trace bounds, without the old table predicate's
fixed dangling scratch pointer and zero capacity.
-/

namespace WNear.Binary.SerdeValueState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (borrowed roomRun code646)
open WNear.Binary.SerdeAccountId (code169)
open WNear.Binary.SerdeDeStrEsc (copiedResult costCopied)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (sbuf endState endFreeBound growthPages)

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The read-only byte tables used by the general string parser. -/
def tables (n : Nat) : IProp GF :=
  iprop(n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
    n ↦[wms][ 1062712 ] SerdeEsc.hexTable)

/-- An empty logical scratch buffer, with any allocated capacity. -/
def scratchPre (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptrS capS sl : UInt32) : IProp GF :=
  iprop(n ↦[i32][ de.toNat + 20 ] sl ∗ n ↦[i32][ de.toNat + 12 ] ptrS ∗
    n ↦[i32][ de.toNat + 16 ] capS ∗ sbuf n maxP hl live F ptrS capS [])

/-- The two live allocations and trace bounds, independently of the reader cursor. -/
def valueStorage (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr capS : UInt32) (bs bytes : List UInt8) (q : Nat) (p c len : UInt32) : IProp GF :=
  iprop(⌜c = UInt32.ofNat bytes.length ∧ len = UInt32.ofNat bytes.length⌝ ∗
    ∃ (scratch cap : UInt32) (hl' F' : Nat),
    ⌜hl ≤ hl' ∧ cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧
      F' = endFreeBound F capS 0 (appendChunks (bs.drop q) []) ∧
      hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop q) []) * 65536⌝ ∗
    n ↦[i32][ de.toNat + 12 ] scratch ∗ n ↦[i32][ de.toNat + 16 ] cap ∗
    n ↦[i32][ de.toNat + 20 ] UInt32.ofNat bytes.length ∗ ParseEscape.sbufR n scratch cap bytes ∗
    SerdeString.heapS n maxP hl' (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live) F'
      (UInt32.ofNat bytes.length) p ∗ n ↦[wms][ p.toNat ] bytes)

/-- The owned value and changed scratch state, independent of the output descriptor's address. -/
def valuePost (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr capS : UInt32) (bs bytes rest : List UInt8) (q : Nat) (p c len : UInt32) : IProp GF :=
  iprop(⌜c = UInt32.ofNat bytes.length ∧ len = UInt32.ofNat bytes.length⌝ ∗
    ∃ (scratch cap : UInt32) (hl' F' : Nat),
    ⌜hl ≤ hl' ∧ cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧
      F' = endFreeBound F capS 0 (appendChunks (bs.drop q) []) ∧
      hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop q) []) * 65536⌝ ∗
    n ↦[i32][ de.toNat + 12 ] scratch ∗ n ↦[i32][ de.toNat + 16 ] cap ∗
    n ↦[i32][ de.toNat + 20 ] UInt32.ofNat bytes.length ∗ ParseEscape.sbufR n scratch cap bytes ∗
    SerdeString.heapS n maxP hl' (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live) F'
      (UInt32.ofNat bytes.length) p ∗ n ↦[wms][ p.toNat ] bytes ∗ rd n de ptr bs (bs.length - rest.length))

/-- Move only the four result words across the caller boundary; retain all heap state. -/
theorem copiedResult_split (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (out de ptr capS : UInt32) (bs bytes rest : List UInt8) (q : Nat) :
    copiedResult (GF := GF) n maxP hl live F out de ptr capS bs bytes rest q ⊢
      ∃ (p c len : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
        n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
        valuePost n maxP hl live F de ptr capS bs bytes rest q p c len := by
  iintro H
  iunfold copiedResult at H
  icases H with ⟨%scratch, %cap, %p, %hl', %F', %htrace, S0, S4, S8, Hscratch, O0, O4, O8, O12, Hheap, Hb, Hrd⟩
  ihave Hheap := SerdeString.heapS_ne $$ Hheap
  icases Hheap with ⟨%hp, Hheap⟩
  iexists p, UInt32.ofNat bytes.length, UInt32.ofNat bytes.length
  isplitr
  · ipureintro; exact hp
  iframe O0 O4 O8 O12
  iunfold valuePost
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists scratch, cap, hl', F'
  iframe S0 S4 S8 Hscratch Hheap Hb Hrd
  ipureintro; exact htrace

/-- Extract the reader cursor while retaining both allocations and all trace bounds. -/
theorem valuePost_split (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr capS : UInt32) (bs bytes rest : List UInt8) (q : Nat) (p c len : UInt32) :
    valuePost (GF := GF) n maxP hl live F de ptr capS bs bytes rest q p c len ⊢
      rd n de ptr bs (bs.length - rest.length) ∗ valueStorage n maxP hl live F de ptr capS bs bytes q p c len := by
  iintro H
  iunfold valuePost at H
  icases H with ⟨%hlen, %scratch, %cap, %hl', %F', %htrace, S0, S4, S8, Hscratch, Hheap, Hb, Hrd⟩
  iframe Hrd
  iunfold valueStorage
  isplitr
  · ipureintro; exact hlen
  iexists scratch, cap, hl', F'
  iframe S0 S4 S8 Hscratch Hheap Hb
  ipureintro; exact htrace

/-- Change the state returned by the abstract 169 boundary. -/
theorem spec169_post {cfg : WasmConfig} {lim : ExecLimits} {d inst n g Cg : Nat} {mi : ModuleInst}
    {gt : GlobalType} {sp de ptr : UInt32} {ob bs : List UInt8} {i K : Nat} {P : IProp GF}
    {Q Q' : UInt32 → UInt32 → UInt32 → IProp GF} (hQ : ∀ p c len, Q p c len ⊢ Q' p c len) :
    SerdeSeqElem.Spec169 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs i P K Q ⊢
      SerdeSeqElem.Spec169 cfg lim d inst mi n g Cg gt sp de ptr ob bs i P K Q' := by
  unfold SerdeSeqElem.Spec169
  apply ParseStrSuccess.spec_post
  intro args rs
  iintro ⟨%hrs, Hg, %p, %c, %len, %hp, O0, O4, O8, O12, HQ⟩
  iframe Hg
  isplitr
  · ipureintro; exact hrs
  iexists p, c, len
  isplitr
  · ipureintro; exact hp
  iframe O0 O4 O8 O12
  iapply hQ p c len
  iexact HQ

/-- Adapt a callee's resource layout at both boundaries without changing its cost. -/
theorem spec_repack {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P P' : List Value → IProp GF} {K : List Value → Nat}
    {Q Q' : List Value → List Value → IProp GF}
    (hP : ∀ args, P' args ⊢ P args) (hQ : ∀ args rs, Q args rs ⊢ Q' args rs) :
    MFunSpec cfg lim d type inst mi code Cg P K Q ⊢ MFunSpec cfg lim d type inst mi code Cg P' K Q' := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R HP Hc
  ihave HP := hP args $$ HP
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

/-- The concrete copied account-id reader supplies 214's abstract callee contract. -/
theorem spec169_copied (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 33 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx sl ptrS capS : UInt32) (ob bs : List UInt8) (value : String)
    (rest : List UInt8) (i j : Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 304 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hj : j = i + wsLen (bs.drop i)) (hjl : j < bs.length) (hq : bs[j]? = some 0x22)
    (hcap : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1))) (hroom : roomRun maxP hl capS [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (hl + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    code169 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      SerdeSeqElem.Spec169 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs i
        iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          scratchPre n maxP hl live F de ptrS capS sl ∗ tables n)
        ((400 + AccountIdValid.cost554 value.toUTF8.toList.length) * cfg.regularOpCost +
          costCopied cfg F capS bs value.toUTF8.toList rest i j)
        (fun p c len => iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗ tables n ∗
          valuePost n maxP hl live F de ptr capS bs value.toUTF8.toList rest (j + 1) p c len)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hs := SerdeAccountIdEsc.f169_copied_model (GF := GF) cfg lim d types[14]! rfl inst mi A n g ta hm hd Cg gt
    (sp - 16) (sp - 16) de ptr idx sl ptrS capS ob bs value rest i j maxP hl live F
    hob (by omega) hlen hptr hde (by omega) hi hj hjl hq hcap hmodel hcopied hroom hvalid halloc
  rw [show (sp - 16).toNat - 288 = sp.toNat - 304 by omega] at hs
  unfold SerdeSeqElem.Spec169
  apply hs.trans
  apply spec_repack
  · intro args
    iintro ⟨%ha, Hg, Ho, Hrd, Hs, Hvt, Hscratch, Htables⟩
    iunfold scratchPre at Hscratch
    icases Hscratch with ⟨S8, S0, S4, Hsb⟩
    iunfold tables at Htables
    icases Htables with ⟨He, Hw, Ht⟩
    iframe Hg Hs Hvt Ho Hrd S8 S0 S4 Hsb He Hw Ht
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, Hs, Hvt, He, Hw, Ht, Hresult⟩
    ihave Hresult := copiedResult_split n maxP hl live F (sp - 16) de ptr capS bs value.toUTF8.toList rest (j + 1) $$ Hresult
    icases Hresult with ⟨%p, %c, %len, %hp, O0, O4, O8, O12, Hvalue⟩
    iframe Hg
    isplitr
    · ipureintro; exact hrs
    iexists p, c, len
    isplitr
    · ipureintro; exact hp
    dsimp only
    iframe O0 O4 O8 O12 Hs Hvt Hvalue
    iunfold tables
    iframe He Hw Ht

end Resource
end WNear.Binary.SerdeValueState
