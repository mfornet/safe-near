import Bridge.Functions.SerdeRej

/-!
# Freeing the parser scratch after a rejecting run

The scratch can be empty or own a live buffer. Its drop has one uniform cost,
independent of the input, gas ceiling and free-list length, and preserves every
allocation that was live before parsing.
-/

namespace WNear.Binary.SerdeRej

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def scratchPre (n maxP len : Nat) (live' : List (Nat × Nat)) (F : Nat)
    (v p c l : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 4 ] c ∗
    n ↦[i32][ v.toNat + 8 ] l ∗ heapInv n maxP len live' F ∗ scrBlk n p c)

def scratchPost (n maxP len : Nat) (live : List (Nat × Nat))
    (v p c l : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 4 ] c ∗
    n ↦[i32][ v.toNat + 8 ] l ∗ ∃ (live'' : List (Nat × Nat)) (F' : Nat),
      ⌜live.Sublist live''⌝ ∗ heapInv n maxP len live'' F')

/-- Dropping an empty or grown scratch preserves the original live allocations. -/
theorem f68_scratch (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg maxP len : Nat)
    (live live' : List (Nat × Nat)) (F : Nat) (v p c l : UInt32)
    (hscr : scrOk live live' p c) (hv : v.toNat + 12 ≤ 2 ^ 32) :
    DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg
        (scratchPre n maxP len live' F v p c l) (fun _ => 315 * cfg.regularOpCost)
        (scratchPost n maxP len live v p c l) := by
  by_cases hc : c = 0
  · subst c
    have hsub : live.Sublist live' := by
      rcases hscr with h | h
      · exact h.2
      · exact False.elim (h.1 rfl)
    iintro #HD
    ihave #HD' := HD
    iunfold DropVec.dropCode at HD'
    icases HD' with ⟨#Hi, _, _, _, _, _, _, _, _, #H747, #H778⟩
    ihave #S := SerdeFromTrait.f68_zero (GF := GF) cfg lim d type htype inst mi A n g ta hm
      (by omega) Cg v (by omega) $$ [Hi H747 H778]
    · iframe Hi H747 H778
    iapply (AllocGen.MFunSpec_cost (K := fun _ => 40 * cfg.regularOpCost) (fun _ => by omega))
    iapply (AllocFresh.MFunSpec_frame
      (Fr := iprop(n ↦[i32][ v.toNat ] p ∗ n ↦[i32][ v.toNat + 8 ] l ∗ heapInv n maxP len live' F))
      (P := fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0))
      (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0)) ?hP ?hQ)
    case hP =>
      intro args
      iintro HP
      iunfold scratchPre at HP
      icases HP with ⟨%ha, H0, H4, H8, Hh, _⟩
      iframe H0 H4 H8 Hh
      ipureintro; exact ha
    case hQ =>
      intro args rs
      iintro ⟨⟨H0, H8, Hh⟩, %hrs, H4⟩
      iunfold scratchPost
      iframe H0 H4 H8
      isplitr
      · ipureintro; exact hrs
      iexists live', F
      iframe Hh
      ipureintro; exact hsub
    iexact S
  · have hs : (p.toNat, c.toNat) ∈ live' ∧ live.Sublist (live'.erase (p.toNat, c.toNat)) := by
      rcases hscr with h | h
      · exact False.elim (hc h.1)
      · exact h.2
    iintro #HD
    ihave #S := DropVec.f68_spec (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg maxP len
      live' F v p c l hc hv $$ HD
    iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
      (P := DropVec.pre747 n maxP len live' F v p c l)
      (Q := DropVec.post747 n maxP len live' F v p c l) ?hP ?hQ)
    case hP =>
      intro args
      iintro HP
      iunfold scratchPre at HP
      icases HP with ⟨%ha, H0, H4, H8, Hh, Hb⟩
      iunfold scrBlk at Hb
      simp only [if_neg hc]
      iunfold DropVec.pre747
      iframe H0 H4 H8 Hh Hb
      ipureintro; exact ⟨ha, hs.1⟩
    case hQ =>
      intro args rs
      iintro ⟨_, HQ⟩
      iunfold DropVec.post747 at HQ
      icases HQ with ⟨%hrs, H0, H4, H8, Hh⟩
      iunfold scratchPost
      iframe H0 H4 H8
      isplitr
      · ipureintro; exact hrs
      iexists live'.erase (p.toNat, c.toNat), F + 1
      iframe Hh
      ipureintro; exact hs.2
    iexact S

end Proof

end WNear.Binary.SerdeRej
