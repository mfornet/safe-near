import Bridge.Functions.SerdeNextKey
import Bridge.Functions.SerdeErrorPositioned

/-!
# Map-key deserialization rejects end of input

`next_key_seed` reports `EofWhileParsingObject` before changing the first-key
flag or touching the scratch. Its error retains the source position needed
by the enclosing struct parser's `fix_position` call.
-/

namespace WNear.Binary.SerdeKeyReject

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr roomFor4)
open WNear.Binary.SerdeEnds (endCode)
open WNear.Binary.SerdeErrorPositioned (heapPos)

/-- The packed `Err(box)` result returned by 193. -/
def errorPack (e : UInt32) : UInt64 := ((1 : UInt64) ||| (512 : UInt64)) ||| (e.toUInt64 <<< 32)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- EOF while reading an object key returns a positioned syntax error. -/
theorem f193_eof (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp acc de ptr idx : UInt32) (fb : UInt8) (bs : List UInt8) (i : Nat)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hacc : acc.toNat + 5 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 176 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hr : roomFor4 mlen maxP 20) (heof : i + wsLen (bs.drop i) = bs.length) :
    endCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f193 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [fb] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 176) 176 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ rd n de ptr bs i))
        (fun _ => (600 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + costErr cfg F (bs.length + 1))
        (fun _ rs => iprop(∃ e : UInt32, ⌜rs = [.i64 (errorPack e)] ∧ e ≠ 0⌝ ∗
          n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [fb] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 176) 176 ∗ vt n 1057464 idx ta (A 578) ∗
          heapPos n maxP mlen live F e ∗ rd n de ptr bs bs.length)) := by
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
  have s339 := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, heof] at s339
  simp only [List.getElem?_eq_none (Nat.le_refl bs.length), SerdeRead.optByte] at s339
  rw [Nat.add_mul] at s339 ⊢
  generalize hW : 96 * w * cfg.regularOpCost = W at s339 ⊢
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hfb, Hg, Hs, Hvt, Hh, Hrd⟩
  subst hargs
  icases stk_split n (sp.toNat - 176) 80 96 $$ Hs with ⟨S80, S96⟩
  icases stk_split n (sp.toNat - 176 + 80) 80 16 $$ S96 with ⟨Sinner, F16⟩
  rw [show sp.toNat - 176 + 80 + 80 = (sp - 16).toNat by omega,
    show sp.toNat - 176 + 80 = (sp - 16).toNat - 80 by omega]
  icases stk_split n (sp - 16).toNat 12 4 $$ F16 with ⟨C12, B12⟩
  iunfold stk at C12
  icases C12 with ⟨%cb, %hcb, C12⟩
  icases U128From.memBytes_split n (sp - 16).toNat 4 cb (by omega) $$ C12 with ⟨C0, C4⟩
  simp only [f193]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep [Hacc]
  mcall s339 using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep [Hacc]; mstep
  mstep; mstep; mstep [C0]
  ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 3) (cb.drop 4) (by simp) $$ [C0 C4]
  · iframe C0 C4
  have s322 := SerdeErrorPositioned.f322_positioned (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 16) de (sp - 16) ptr idx (bytes32 3 ++ cb.drop 4) bs bs.length
    maxP mlen live F (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hr
  rw [hE] at s322
  ihave #S322 := s322 $$ [Hcode F640]
  · iframe Hcode F640
  clear s322
  mstep; mstep
  mcall S322 using [Hg Sinner Hvt Hh C Hrd]
  · iframe Hg Sinner Hvt Hh C Hrd
  icases HQ with ⟨%e, %⟨hrs, he⟩, Hg, Sinner, Hvt, HE, C, Hrd⟩
  subst hrs
  mcredits (30 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists e
  isplitr
  · ipureintro; simp [htype, errorPack, he]
  iframe Hacc Hfb Hg Hvt HE Hrd
  ihave C := stk_intro n (sp - 16).toNat (bytes32 3 ++ cb.drop 4) $$ C
  simp only [List.length_append, bytes32_length, List.length_drop, hcb]
  ihave S16 := stk_join n (sp - 16).toNat 12 4 $$ [C B12]
  · iframe C B12
  ihave Sinner := stk_addr (show (sp - 16).toNat - 80 = sp.toNat - 176 + 80 by omega) $$ Sinner
  ihave S16 := stk_addr (show (sp - 16).toNat = sp.toNat - 176 + 80 + 80 by omega) $$ S16
  ihave S96 := stk_join n (sp.toNat - 176 + 80) 80 16 $$ [Sinner S16]
  · iframe Sinner S16
  iapply stk_join n (sp.toNat - 176) 80 96
  iframe S80 S96

end Proof

end WNear.Binary.SerdeKeyReject
