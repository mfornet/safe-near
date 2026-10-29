import Bridge.Functions.SerdeErrorCode
import Bridge.Functions.SerdeEnds

/-! # EOF in the closing-object check retains the exact syntax error code -/

namespace WNear.Binary.SerdeEndMapEOF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr roomFor4)
open WNear.Binary.SerdeEnds (endCode)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem f90_eof (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat)
    (maxP mlen F : Nat) (live : List (Nat × Nat))
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hr : roomFor4 mlen maxP 20) (heof : i + wsLen (bs.drop i) = bs.length) :
    endCode n maxP inst mi A ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f90 Cg
      (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
        heapInv n maxP mlen live F ∗ rd n de ptr bs i))
      (fun _ => (400 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + costErr cfg F (bs.length + 1))
      (fun _ rs => iprop(∃ (p : UInt32) (b8 : List UInt8), ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ b8.length = 8⌝ ∗
        g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
        SerdeErrorCode.heapPos n maxP mlen live F p (bytes32 3 ++ b8) ∗ rd n de ptr bs bs.length)) := by
  iintro #Hv
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, #F640, #F322, #F332, #F333, #F339⟩
  ihave #Hcode' := Hcode
  iunfold errCode at Hcode'
  icases Hcode' with ⟨#H310c, _, _, _, _, _, _, _, _, _⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha322 := hm.funcs 322 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have t13 : types[13]!.params.length = 2 := rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  generalize hw : wsLen (bs.drop i) = w at heof ⊢
  generalize hE : costErr cfg F (bs.length + 1) = E
  simp only [Nat.add_mul]
  generalize hW : 96 * w * cfg.regularOpCost = W
  have s339 := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, heof] at s339
  simp only [List.getElem?_eq_none (Nat.le_refl bs.length), SerdeRead.optByte, Nat.add_mul] at s339
  rw [hW] at s339
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, Hs, Hvt, Hh, Hrd⟩
  subst ha
  simp only [f90]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall s339 using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (250 * cfg.regularOpCost + E + R)
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  icases stk_split n (sp.toNat - 96) 80 16 $$ Hs with ⟨S80, F16⟩
  rw [show sp.toNat - 96 + 80 = (sp - 16).toNat by omega]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  iunfold stk at F16
  icases F16 with ⟨%b16, %hb16, F16⟩
  icases U128From.memBytes_split n (sp - 16).toNat 4 b16 (by omega) $$ F16 with ⟨B0, B4⟩
  mstep; mstep; mstep [B0] with (simp; omega)
  icases U128From.memBytes_split n ((sp - 16).toNat + 4) 8 (b16.drop 4) (by simp; omega) $$ B4 with ⟨B4, B12⟩
  ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 3) ((b16.drop 4).take 8) (by simp) $$ [B0 B4]
  · iframe B0 B4
  mstep; mstep; mstep
  ihave S80 := stk_addr (show sp.toNat - 96 = (sp - 16).toNat - 80 by omega) $$ S80
  have s322 := SerdeErrorCode.f322_positioned (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 16) de (sp - 16) ptr idx (bytes32 3 ++ (b16.drop 4).take 8) bs bs.length
    maxP mlen live F (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hr
  rw [hE] at s322
  ihave #S322 := s322 $$ [Hcode F640]
  · iframe Hcode F640
  mcall S322 using [Hg S80 Hvt Hh C Hrd]
  · iframe Hg S80 Hvt Hh C Hrd
  icases HQ with ⟨%p, %⟨hrs, hp⟩, Hg, S80, Hvt, HA, C, Hrd⟩
  subst hrs
  mstep
  mstep
  mctrl_norm
  repeat mpay
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p, (b16.drop 4).take 8
  isplitr
  · ipureintro; simp [htype, hp]; omega
  iframe Hg Hvt HA Hrd
  ihave C := stk_intro n _ _ $$ C
  rw [show (bytes32 3 ++ (b16.drop 4).take 8).length = 12 by simp; omega]
  ihave B12 := stk_intro n _ _ $$ B12
  rw [show ((b16.drop 4).drop 8).length = 4 by simp; omega]
  ihave F16 := stk_join n (sp - 16).toNat 12 4 $$ [C B12]
  · rw [show (sp - 16).toNat + 12 = (sp - 16).toNat + 4 + 8 by omega]; iframe C B12
  ihave S80 := stk_addr (show (sp - 16).toNat - 80 = sp.toNat - 96 by omega) $$ S80
  ihave F16 := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ F16
  iapply stk_join n (sp.toNat - 96) 80 16
  iframe S80 F16

end Proof
end WNear.Binary.SerdeEndMapEOF
