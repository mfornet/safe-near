import Bridge.Functions.SerdeValueReuse
import Bridge.Functions.SerdeFromTrait
import Bridge.Functions.SerdeScratchValueDrop

/-! Successful account-id array parsing for both borrowed and copied strings. -/
namespace WNear.Binary.SerdeValueReuse
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.ParseStrSuccess (appendChunks)

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Empty and grown scratch cleanup keeps its exact one-cell allocator bound. -/
theorem f68_scratch_exact (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (v ptr cap sl : UInt32)
    (hv : v.toNat + 12 ≤ 2 ^ 32) :
    DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] ptr ∗
          n ↦[i32][ v.toNat + 4 ] cap ∗ n ↦[i32][ v.toNat + 8 ] sl ∗
          ScratchGrow.sbuf n maxP hl live F ptr cap []))
        (fun _ => 315 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] ptr ∗
          n ↦[i32][ v.toNat + 4 ] cap ∗ n ↦[i32][ v.toNat + 8 ] sl ∗
          heapInv n maxP hl live (F + 1))) := by
  by_cases hc : cap = 0
  · subst cap
    iintro #HD
    ihave #HD' := HD
    iunfold DropVec.dropCode at HD'
    icases HD' with ⟨#Hi, _, _, _, _, _, _, _, _, #H747, #H778⟩
    ihave #S := SerdeFromTrait.f68_zero (GF := GF) cfg lim d type htype inst mi A n g ta hm
      (by omega) Cg v (by omega) $$ [Hi H747 H778]
    · iframe Hi H747 H778
    iapply (AllocGen.MFunSpec_cost (K := fun _ => 40 * cfg.regularOpCost) (fun _ => by omega))
    iapply (AllocFresh.MFunSpec_frame
      (Fr := iprop(n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 8 ] sl ∗ heapInv n maxP hl live F))
      (P := fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0))
      (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0)) ?hP ?hQ)
    case hP =>
      intro args
      iintro ⟨%ha, S0, S4, S8, Hscratch⟩
      iunfold ScratchGrow.sbuf at Hscratch
      simp only [ite_true]
      icases Hscratch with ⟨_, _, _, Hheap⟩
      iframe S0 S4 S8 Hheap
      ipureintro; exact ha
    case hQ =>
      intro args rs
      iintro ⟨⟨S0, S8, Hheap⟩, %hrs, S4⟩
      iframe S0 S4 S8
      isplitr
      · ipureintro; exact hrs
      iapply heapInv_mono n maxP hl live F (F + 1) (by omega)
      iexact Hheap
    iexact S
  · have hs := DropVec.f68_spec (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg maxP hl
      ((ptr.toNat, cap.toNat) :: live) F v ptr cap sl hc hv
    apply hs.trans
    apply SerdeValueState.spec_repack
    · intro args
      iintro ⟨%ha, S0, S4, S8, Hscratch⟩
      iunfold ScratchGrow.sbuf at Hscratch
      simp only [if_neg hc]
      icases Hscratch with ⟨_, _, ⟨%junk, %hjunk, Hjunk⟩, Hheap⟩
      iunfold DropVec.pre747
      iframe S0 S4 S8 Hheap
      isplitr
      · ipureintro; exact ha
      isplitr
      · ipureintro; simp
      iunfold block
      iexists junk
      isplitr
      · ipureintro; simpa using hjunk
      simp only [List.length_nil, Nat.add_zero]
      iexact Hjunk
    · intro args rs
      simp only [DropVec.post747, List.erase_cons_head]
      iintro ⟨%hrs, S0, S4, S8, Hheap⟩
      iframe S0 S4 S8 Hheap
      ipureintro; exact hrs

/-- Cleanup of either owned-string path retains the concrete parser/copy growth bounds. -/
theorem f68_owned_value (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (de capS p c len : UInt32) (bs bytes : List UInt8) (q : Nat)
    (hde : de.toNat + 24 ≤ 2 ^ 32) :
    DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg
        (fun args => iprop(⌜args = [.i32 (de + 12)]⌝ ∗ ownedValue n maxP hl live F de capS bs bytes q p c len))
        (fun _ => 315 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ scratch cap sl : UInt32,
          n ↦[i32][ de.toNat + 12 ] scratch ∗ n ↦[i32][ de.toNat + 16 ] cap ∗
          n ↦[i32][ de.toNat + 20 ] sl ∗
          SerdeScratchValueDrop.cleanValue n maxP hl live F capS bs bytes q p c len)) := by
  have hde12 : (de + 12).toNat = de.toNat + 12 := by rw [UInt32.toNat_add]; simp; omega
  iintro #HD
  unfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Howned⟩
  iunfold ownedValue at Howned
  icases Howned with ⟨%⟨hc, hlen, hp⟩, Hb, %scratch, %cap, %sl, %hl', %ht, Hscratch⟩
  subst hc hlen
  iunfold SerdeValueState.scratchPre at Hscratch
  icases Hscratch with ⟨S8, S0, S4, Hsb⟩
  have hs := f68_scratch_exact (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg maxP hl'
    ((p.toNat, (UInt32.ofNat bytes.length).toNat) :: live)
    (max (ScratchGrow.endFreeBound F capS 0 (appendChunks (bs.drop q) [])) 1)
    (de + 12) scratch cap sl (by omega)
  ihave #S := hs $$ HD
  ihave HP : iprop(⌜args = [.i32 (de + 12)]⌝ ∗
      n ↦[i32][ (de + 12).toNat ] scratch ∗ n ↦[i32][ (de + 12).toNat + 4 ] cap ∗
      n ↦[i32][ (de + 12).toNat + 8 ] sl ∗
      ScratchGrow.sbuf n maxP hl' ((p.toNat, (UInt32.ofNat bytes.length).toNat) :: live)
        (max (ScratchGrow.endFreeBound F capS 0 (appendChunks (bs.drop q) [])) 1) scratch cap [])
      $$ [S0 S4 S8 Hsb]
  · rw [hde12]
    rw [show de.toNat + 12 + 4 = de.toNat + 16 by omega, show de.toNat + 12 + 8 = de.toNat + 20 by omega]
    iframe S0 S4 S8 Hsb
    ipureintro; exact ha
  iunfold MFunSpec at S
  iapply mwpInvoke_wand
  isplitl [HP Hc]
  · iapply S $$ %args %R HP Hc
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %hrs, S0, S4, S8, Hheap⟩
    iframe Hc
    isplitr
    · ipureintro; exact hrs
    iexists scratch, cap, sl
    rw [hde12]
    rw [show de.toNat + 12 + 4 = de.toNat + 16 by omega, show de.toNat + 12 + 8 = de.toNat + 20 by omega]
    iframe S0 S4 S8
    iunfold SerdeScratchValueDrop.cleanValue
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hp⟩
    iframe Hb
    iexists hl', max (ScratchGrow.endFreeBound F capS 0 (appendChunks (bs.drop q) [])) 1 + 1
    iframe Hheap
    ipureintro; exact ⟨ht.2.1, ht.2.2, rfl⟩
  · iintro HT; iexact HT

end Spec
end WNear.Binary.SerdeValueReuse
