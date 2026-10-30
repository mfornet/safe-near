import Bridge.Functions.SerdeValueState
import Bridge.Functions.DropVec

/-!
# Scratch cleanup preserving the deserialized account-id allocation

The owned String is first in the allocator's live list and scratch is second.
The actual Vec drop removes scratch, keeps the String and all earlier live
allocations, and retains the memory/free-list bounds needed by outer callers.
-/

namespace WNear.Binary.SerdeScratchValueDrop

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeValueState (valueStorage)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endFreeBound growthPages)

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Distinct live allocator entries have distinct data pointers. -/
theorem heapInv_distinct_heads (n maxP hl p size scratch cap : Nat)
    (live : List (Nat × Nat)) (F : Nat) :
    heapInv (GF := GF) n maxP hl ((p, size) :: (scratch, cap) :: live) F ⊢
      ⌜p ≠ scratch⌝ ∗ heapInv n maxP hl ((p, size) :: (scratch, cap) :: live) F := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hw, hlen⟩, Hhead, Hlen, Hmax, Hcells⟩
  isplitr
  · ipureintro
    have hd := hw.lives.live_nodup
    simp only [List.map_cons, List.nodup_cons] at hd
    intro he
    exact hd.1 (by simp [he])
  iunfold heapInv
  iexists M
  iframe Hhead Hlen Hmax Hcells
  ipureintro; exact ⟨hw, hlen⟩

/-- A newly constructed deserializer has an empty dangling scratch and the original heap. -/
theorem empty_scratch (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) :
    heapInv (GF := GF) n maxP hl live F ⊢ ScratchGrow.sbuf n maxP hl live F 1 0 [] := by
  iintro Hheap
  iunfold ScratchGrow.sbuf
  simp only [if_pos rfl, ite_true]
  iframe Hheap
  isplitr
  · ipureintro; decide
  isplitl []
  · iapply ScratchGrow.memBytes_nil
  iexists ([] : List UInt8)
  isplitr
  · ipureintro; rfl
  iapply ScratchGrow.memBytes_nil

/-- Only the owned value remains live, with total parser/copy growth and the post-drop allocator bound. -/
def cleanValue (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (capS : UInt32)
    (bs bytes : List UInt8) (q : Nat) (p c len : UInt32) : IProp GF :=
  iprop(⌜c = UInt32.ofNat bytes.length ∧ len = UInt32.ofNat bytes.length ∧ p ≠ 0⌝ ∗
    n ↦[wms][ p.toNat ] bytes ∗ ∃ (hl' F' : Nat),
    ⌜hl ≤ hl' ∧
      hl' ≤ hl + (growthPages capS 0 (appendChunks (bs.drop q) []) +
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bytes.length)) 1).toNat) * 65536 ∧
      F' = max (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) 1 + 1⌝ ∗
    heapInv n maxP hl' ((p.toNat, c.toNat) :: live) F')

set_option maxRecDepth 100000 in
/-- Free the grown scratch with the actual 68 call, retaining the owned value and earlier allocations. -/
theorem f68_value (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (de ptr capS p c len : UInt32) (bs bytes : List UInt8) (q : Nat)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hpos : 0 < bytes.length) (hlen : bytes.length < 2 ^ 32) :
    DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg
        (fun args => iprop(⌜args = [.i32 (de + 12)]⌝ ∗
          valueStorage n maxP hl live F de ptr capS bs bytes q p c len))
        (fun _ => 315 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (scratch cap : UInt32),
          n ↦[i32][ de.toNat + 12 ] scratch ∗ n ↦[i32][ de.toNat + 16 ] cap ∗
          n ↦[i32][ de.toNat + 20 ] UInt32.ofNat bytes.length ∗
          cleanValue n maxP hl live F capS bs bytes q p c len)) := by
  have hm32 : (UInt32.ofNat bytes.length).toNat = bytes.length := by simp; omega
  have hs0 : UInt32.ofNat bytes.length ≠ 0 := by
    intro he
    have he' := congrArg UInt32.toNat he
    rw [hm32] at he'
    change bytes.length = 0 at he'
    omega
  have hde12 : (de + 12).toNat = de.toNat + 12 := by rw [UInt32.toNat_add]; simp; omega
  iintro #HD
  unfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hvalue⟩
  iunfold valueStorage at Hvalue
  icases Hvalue with ⟨%⟨hc, hlenEq⟩, %scratch, %cap, %hl1, %F1, %htrace, S0, S4, S8, Hscratch, Hheap, Hb⟩
  subst hc hlenEq
  iunfold ParseEscape.sbufR at Hscratch
  icases Hscratch with ⟨%hbuf, Hscratch, %junk, %hjunk, Hjunk⟩
  have hcap : cap ≠ 0 := by
    intro he
    have he' := congrArg UInt32.toNat he
    change cap.toNat = 0 at he'
    omega
  iunfold SerdeString.heapS at Hheap
  simp only [if_neg hs0, if_neg hcap]
  icases Hheap with ⟨%⟨hp, hpbound⟩, %hl2, %hgrown, Hheap⟩
  rw [hm32]
  ihave Hheap := heapInv_distinct_heads n maxP hl2 p.toNat bytes.length scratch.toNat cap.toNat live (max F1 1) $$ Hheap
  icases Hheap with ⟨%hne, Hheap⟩
  have hpair : (p.toNat, bytes.length) ≠ (scratch.toNat, cap.toNat) := by
    intro he; exact hne (congrArg Prod.fst he)
  have herase : (((p.toNat, bytes.length) :: (scratch.toNat, cap.toNat) :: live).erase
      (scratch.toNat, cap.toNat)) = (p.toNat, bytes.length) :: live := by
    simp [List.erase_cons, hpair]
  ihave Hjoined := U128From.memBytes_join n scratch.toNat bytes.length bytes junk rfl $$ [Hscratch Hjunk]
  · iframe Hscratch Hjunk
  ihave Hblock : block n scratch.toNat cap.toNat $$ [Hjoined]
  · iunfold block
    iexists bytes ++ junk
    iframe Hjoined
    ipureintro; simp only [List.length_append]; omega
  have key := DropVec.f68_spec (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg maxP hl2
    ((p.toNat, bytes.length) :: (scratch.toNat, cap.toNat) :: live) (max F1 1)
    (de + 12) scratch cap (UInt32.ofNat bytes.length) hcap (by omega)
  ihave #S := key $$ HD
  clear key
  ihave Hpre : DropVec.pre747 n maxP hl2 ((p.toNat, bytes.length) :: (scratch.toNat, cap.toNat) :: live)
      (max F1 1) (de + 12) scratch cap (UInt32.ofNat bytes.length) args $$ [S0 S4 S8 Hheap Hblock]
  · iunfold DropVec.pre747
    rw [hde12]
    rw [show de.toNat + 12 + 4 = de.toNat + 16 by omega, show de.toNat + 12 + 8 = de.toNat + 20 by omega]
    iframe S0 S4 S8 Hheap Hblock
    ipureintro; exact ⟨ha, by simp⟩
  iunfold MFunSpec at S
  iapply mwpInvoke_wand
  isplitl [Hpre Hc]
  · iapply S $$ %args %R Hpre Hc
  isplit
  · dsimp only
    iintro %rs ⟨Hc, HQ⟩
    iunfold DropVec.post747 at HQ
    icases HQ with ⟨%hrs, S0, S4, S8, Hheap⟩
    rw [herase]
    iframe Hc
    isplitr
    · ipureintro; exact hrs
    iexists scratch, cap
    rw [hde12]
    rw [show de.toNat + 12 + 4 = de.toNat + 16 by omega, show de.toNat + 12 + 8 = de.toNat + 20 by omega]
    iframe S0 S4 S8
    iunfold cleanValue
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hp⟩
    iframe Hb
    iexists hl2, max F1 1 + 1
    rw [hm32]
    iframe Hheap
    ipureintro
    have hg : hl1 ≤ hl2 ∧ hl2 ≤ hl1 +
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bytes.length)) 1).toNat * 65536 := by
      unfold VecFromElem.grownLen at hgrown
      rcases hgrown with he | he <;> omega
    refine ⟨by omega, ?_, ?_⟩
    · have hb := htrace.2.2.2
      simp only [Nat.add_mul]
      omega
    · rw [htrace.2.2.1]
  · iintro HT; iexact HT

end Resource
end WNear.Binary.SerdeScratchValueDrop
