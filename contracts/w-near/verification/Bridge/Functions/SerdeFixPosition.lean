import Bridge.Functions.SerdeErrorPositioned

/-!
# Already-positioned errors are preserved by `fix_position`

Syntax errors carry a nonzero source line. The branch that reparses the
position and drops the old error is therefore unreachable for them.
-/

namespace WNear.Binary.SerdeErrorPositioned

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- `Error::fix_position` returns an already-positioned box unchanged. -/
theorem f327_positioned (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (A : Nat → Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType)
    (sp e de : UInt32) (hsp : 16 ≤ sp.toNat) :
    inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f327 Cg
        (fun args => iprop(⌜args = [.i32 e, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ positionedBox n e))
        (fun _ => 60 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 e]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ positionedBox n e)) := by
  iintro #Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HE⟩
  subst hargs
  iunfold positionedBox at HE
  icases HE with ⟨%code, %line, %col, %⟨he, hc, hl⟩, Hcode, Hline, Hcol⟩
  simp only [f327]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mstep; mstep [Hline]; mstep
  mstep_not_taken with simp [Numeric.bool, hl]
  mstep; mstep; mstep
  mcredits (10 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hs
  isplitr
  · ipureintro; simp [htype]
  iunfold positionedBox
  iexists code, line, col
  iframe Hcode Hline Hcol
  ipureintro; exact ⟨he, hc, hl⟩

set_option maxRecDepth 100000 in
/-- The deserializer wrapper (326) also preserves an already-positioned error. -/
theorem f326_positioned (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp de e : UInt32) (hsp : 16 ≤ sp.toNat) :
    inst ↪[inst] mi ∗ A 327 ↪[wf] FuncInst.wasm types[13]! inst f327 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f326 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 e]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ positionedBox n e))
        (fun _ => 100 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 e]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ positionedBox n e)) := by
  iintro ⟨#Hi, #F327⟩
  have ha327 := hm.funcs 327 (by decide)
  have t13 : types[13]!.params.length = 2 := rfl
  ihave #S := f327_positioned (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi n g ta A hm Cg gt sp e de hsp $$ Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HE⟩
  subst hargs
  simp only [f326]
  mstep; mstep
  mcall S using [Hg Hs HE]
  · iframe Hg Hs HE
  icases HQ with ⟨%hrs, Hg, Hs, HE⟩
  subst hrs
  repeat mstep
  iapply NearLogic.mfunc_normal_intro'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; simp [htype]
  iintro Hc
  simp only [htype, List.length_cons, List.length_nil, Nat.sub_self, List.drop_zero]
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hs HE

end Proof

end WNear.Binary.SerdeErrorPositioned
