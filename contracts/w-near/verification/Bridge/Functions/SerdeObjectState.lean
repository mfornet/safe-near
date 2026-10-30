import Bridge.Functions.SerdeKeyEsc
import Bridge.Functions.AllocLivePerm

/-!
# Reusable scratch state across object members

Keys and the account-id value may change the scratch allocation. After a value,
the String stays live while scratch is reordered to the head of the logical
allocation list, so the same key reader can run again.
-/

namespace WNear.Binary.SerdeObjectState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.ScratchGrow (sbuf capAfter endState endFreeBound growthCount growthPages validTrace)
open WNear.Binary.ParseStr (strRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.SerdeValueState (scratchPre valueStorage)

/-- A reserve needs at most the old capacity, eight bytes, or twice the new used length. -/
theorem capAfter_reuse (cap len k : UInt32) (hc : cap.toNat < 2 ^ 30)
    (hadd : len.toNat + k.toNat < 2 ^ 32) :
    (capAfter cap len k).toNat ≤ max cap.toNat (max 8 (2 * (len + k).toNat)) := by
  unfold capAfter
  split
  · omega
  · rename_i hfit
    have hsum : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
    rw [VecGrow.growCap_toNat _ _ hc, hsum]
    simp only [ScratchGrow.fits] at hfit
    omega

/-- The sharper capacity bound is stable over a complete append trace. -/
theorem endState_reuse (cap len : UInt32) (ks : List UInt32) (hv : validTrace cap len ks) :
    (endState cap len ks).1.toNat ≤ max cap.toNat (max 8 (2 * (endState cap len ks).2.toNat)) := by
  induction ks generalizing cap len with
  | nil => simp [endState]
  | cons k ks ih =>
    obtain ⟨_, hc, hadd, hv⟩ := hv
    have hs := capAfter_reuse cap len k hc hadd
    have hr := ih (capAfter cap len k) (len + k) hv
    have hl := ScratchGrow.endState_len (capAfter cap len k) (len + k) ks hv
    simp only [endState]
    omega

/-- A successful string preserves the capacity premise required by the next general string call. -/
theorem parsed_capacity (bs bytes rest : List UInt8) (q : Nat) (cap : UInt32)
    (hlen : bs.length < 2 ^ 24) (hcap : cap.toNat < 2 ^ 25)
    (hok : strRun (bs.drop q) [] = .ok bytes rest) :
    (endState cap 0 (appendChunks (bs.drop q) [])).1.toNat < 2 ^ 25 := by
  have hv := ParseStrSuccess.appendChunks_valid cap [] (bs.drop q) bytes rest hok (by simp) (by omega) (by simp; omega)
  have hc := endState_reuse cap 0 (appendChunks (bs.drop q) []) hv.1
  have hl := SerdeDeStrEsc.strRun_size (bs.drop q) [] bytes rest hok
  simp only [List.length_nil, Nat.zero_add, List.length_drop] at hl
  have hn := hv.2.1
  simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hv hn
  omega

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Normalize either key result to existential scratch coordinates and bounds for the next member. -/
theorem keyState_reuse (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr ptrS capS : UInt32) (bs bytes rest : List UInt8) (q : Nat)
    (hlen : bs.length < 2 ^ 24) (hcap : capS.toNat < 2 ^ 25)
    (hok : strRun (bs.drop q) [] = .ok bytes rest) :
    SerdeKeyEsc.keyState (GF := GF) n maxP hl live F de ptr ptrS capS bs bytes rest q ⊢
      ∃ (p cap sl : UInt32) (hl' F' : Nat),
        ⌜cap.toNat < 2 ^ 25 ∧ hl ≤ hl' ∧
          hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop q) []) * 65536 ∧
          F' ≤ F + 2 * growthCount capS 0 (appendChunks (bs.drop q) [])⌝ ∗
        SerdeRead.rd n de ptr bs (bs.length - rest.length) ∗ scratchPre n maxP hl' live F' de p cap sl := by
  iintro H
  iunfold SerdeKeyEsc.keyState at H
  icases H with ⟨Hrd, Hs⟩
  by_cases hb : ParseStr.borrowed (bs.drop q)
  · simp only [if_pos hb]
    iexists ptrS, capS, 0, hl, F
    iframe Hrd Hs
    ipureintro; exact ⟨hcap, le_rfl, by omega, by omega⟩
  · simp only [if_neg hb]
    icases Hs with ⟨%p, %cap, %hl', %F', %ht, Hs⟩
    iexists p, cap, UInt32.ofNat bytes.length, hl', F'
    iframe Hrd Hs
    ipureintro
    have hc := parsed_capacity bs bytes rest q capS hlen hcap hok
    have hf := ScratchGrow.endFreeBound_eq F capS 0 (appendChunks (bs.drop q) [])
    exact ⟨ht.2.1 ▸ hc, ht.1, ht.2.2.2, by omega⟩

/-- Retain the owned String while making value-reader scratch reusable by subsequent object keys. -/
theorem valueStorage_reuse (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr capS : UInt32) (bs bytes : List UInt8) (q : Nat) (p c len : UInt32)
    (hbytes : 0 < bytes.length) (hsmall : bytes.length < 2 ^ 32) :
    valueStorage (GF := GF) n maxP hl live F de ptr capS bs bytes q p c len ⊢
      ⌜c = UInt32.ofNat bytes.length ∧ len = UInt32.ofNat bytes.length ∧ p ≠ 0⌝ ∗
      n ↦[wms][ p.toNat ] bytes ∗ ∃ (scratch cap : UInt32) (hl' : Nat),
        ⌜cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧ hl ≤ hl' ∧
          hl' ≤ hl + (growthPages capS 0 (appendChunks (bs.drop q) []) +
            (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bytes.length)) 1).toNat) * 65536⌝ ∗
        scratchPre n maxP hl' ((p.toNat, c.toNat) :: live)
          (max (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) 1)
          de scratch cap (UInt32.ofNat bytes.length) := by
  have hm : (UInt32.ofNat bytes.length).toNat = bytes.length := by
    change bytes.length % 2 ^ 32 = bytes.length
    exact Nat.mod_eq_of_lt hsmall
  have hs : UInt32.ofNat bytes.length ≠ 0 := by
    intro he
    have h := congrArg UInt32.toNat he
    rw [hm] at h
    change bytes.length = 0 at h
    omega
  iintro H
  iunfold valueStorage at H
  icases H with ⟨%⟨hc, hlen⟩, %scratch, %cap, %hl1, %F1, %ht, S0, S4, S8, Hscratch, Hheap, Hb⟩
  subst hc hlen
  iunfold SerdeString.heapS at Hheap
  simp only [if_neg hs]
  icases Hheap with ⟨%⟨hp, hpbound⟩, %hl2, %hg, Hheap⟩
  isplitr
  · ipureintro; exact ⟨True.intro, True.intro, hp⟩
  iframe Hb
  iexists scratch, cap, hl2
  isplitr
  · ipureintro
    have hh : hl1 ≤ hl2 ∧ hl2 ≤ hl1 +
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bytes.length)) 1).toNat * 65536 := by
      unfold VecFromElem.grownLen at hg
      rcases hg with he | he <;> omega
    refine ⟨ht.2.1, by omega, ?_⟩
    have hb := ht.2.2.2
    simp only [Nat.add_mul]
    omega
  have hperm : ((p.toNat, (UInt32.ofNat bytes.length).toNat) ::
      (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live)).Perm
      (if cap = 0 then (p.toNat, (UInt32.ofNat bytes.length).toNat) :: live
        else (scratch.toNat, cap.toNat) :: (p.toNat, (UInt32.ofNat bytes.length).toNat) :: live) := by
    split
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _
  ihave Hheap := heapInv_perm n maxP hl2 _ _ (max F1 1) hperm $$ Hheap
  ihave Hjoined := ParseEscape.sbuf_join $$ [Hheap Hscratch]
  · iframe Hheap Hscratch
  ihave Hempty := SerdeKeyEsc.sbuf_clear n maxP hl2
    ((p.toNat, (UInt32.ofNat bytes.length).toNat) :: live) (max F1 1) scratch cap bytes $$ Hjoined
  iunfold scratchPre
  rw [ht.2.2.1]
  iframe S0 S4 S8 Hempty

end Resource
end WNear.Binary.SerdeObjectState
