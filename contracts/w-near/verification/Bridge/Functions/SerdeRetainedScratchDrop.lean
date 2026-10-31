import Bridge.Functions.SerdeValueState
import Bridge.Functions.SerdeFromTrait

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
/-- Drop the retained scratch and preserve the complete original live list. -/
theorem f68_retained_scratch (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (de ptr cap sl : UInt32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) :
    DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg
        (fun args => iprop(⌜args = [.i32 (de + 12)]⌝ ∗ SerdeValueState.scratchPre n maxP hl live F de ptr cap sl))
        (fun _ => 315 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ de.toNat + 12 ] ptr ∗
          n ↦[i32][ de.toNat + 16 ] cap ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          WNear.Binary.AllocInv.heapInv n maxP hl live (F + 1))) := by
  have hv : (de + 12).toNat = de.toNat + 12 := by rw [UInt32.toNat_add]; simp; omega
  by_cases hc : cap = 0
  · subst cap
    iintro #HD
    ihave #HD' := HD
    iunfold DropVec.dropCode at HD'
    icases HD' with ⟨#Hi, _, _, _, _, _, _, _, _, #H747, #H778⟩
    ihave #S := SerdeFromTrait.f68_zero (GF := GF) cfg lim d type htype inst mi A n g ta hm
      (by omega) Cg (de + 12) (by rw [hv]; omega) $$ [Hi H747 H778]
    · iframe Hi H747 H778
    iapply (AllocGen.MFunSpec_cost (K := fun _ => 40 * cfg.regularOpCost) (fun _ => by omega))
    iapply (AllocFresh.MFunSpec_frame
      (Fr := iprop(n ↦[i32][ de.toNat + 12 ] ptr ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
        WNear.Binary.AllocInv.heapInv n maxP hl live F))
      (P := fun args => iprop(⌜args = [.i32 (de + 12)]⌝ ∗ n ↦[i32][ (de + 12).toNat + 4 ] 0))
      (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ (de + 12).toNat + 4 ] 0)) ?hP ?hQ)
    case hP =>
      intro args
      iintro ⟨%ha, HS⟩
      iunfold SerdeValueState.scratchPre at HS
      icases HS with ⟨S20, S12, S16, Hb⟩
      iunfold ScratchGrow.sbuf at Hb
      isimp only [ite_true] at Hb
      icases Hb with ⟨_, _, _, Hh⟩
      rw [hv, show de.toNat + 12 + 4 = de.toNat + 16 by omega]
      iframe S12 S20 S16 Hh
      ipureintro; exact ha
    case hQ =>
      intro args rs
      iintro ⟨⟨S12, S20, Hh⟩, %hrs, S16⟩
      rw [hv, show de.toNat + 12 + 4 = de.toNat + 16 by omega]
      ihave Hh := WNear.Binary.AllocInv.heapInv_mono n maxP hl live F (F + 1) (by omega) $$ Hh
      iframe S12 S20 S16 Hh
      ipureintro; exact hrs
    iexact S
  · iintro #HD
    ihave #S := DropVec.f68_spec (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg maxP hl
      ((ptr.toNat, cap.toNat) :: live) F (de + 12) ptr cap sl hc (by rw [hv]; omega) $$ HD
    iapply (SerdeValueState.spec_repack
      (P := DropVec.pre747 n maxP hl ((ptr.toNat, cap.toNat) :: live) F (de + 12) ptr cap sl)
      (Q := DropVec.post747 n maxP hl ((ptr.toNat, cap.toNat) :: live) F (de + 12) ptr cap sl) ?hP ?hQ)
    case hP =>
      intro args
      iintro ⟨%ha, HS⟩
      iunfold SerdeValueState.scratchPre at HS
      icases HS with ⟨S20, S12, S16, Hb⟩
      iunfold ScratchGrow.sbuf at Hb
      isimp only [if_neg hc, List.length_nil, Nat.add_zero, Nat.sub_zero] at Hb
      icases Hb with ⟨%hb, _, Hrest, Hh⟩
      icases Hrest with ⟨%junk, %hjunk, Hbytes⟩
      iunfold DropVec.pre747, WNear.Binary.AllocInv.block
      rw [hv, show de.toNat + 12 + 4 = de.toNat + 16 by omega,
        show de.toNat + 12 + 8 = de.toNat + 20 by omega]
      iframe S12 S16 S20 Hh
      isplitr
      · ipureintro; exact ha
      isplitr
      · ipureintro; simp
      iexists junk
      iframe Hbytes
      ipureintro; exact hjunk
    case hQ =>
      intro args rs
      iintro HQ
      iunfold DropVec.post747 at HQ
      icases HQ with ⟨%hrs, S12, S16, S20, Hh⟩
      rw [hv, show de.toNat + 12 + 4 = de.toNat + 16 by omega,
        show de.toNat + 12 + 8 = de.toNat + 20 by omega]
      isimp only [List.erase_cons_head] at Hh
      iframe S12 S16 S20 Hh
      ipureintro; exact hrs
    iexact S


end Resource
end WNear.Binary.SerdeObjectMixedTrace
