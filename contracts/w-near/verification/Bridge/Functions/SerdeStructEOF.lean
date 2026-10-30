import Bridge.Functions.SerdeRej

/-!
# Struct deserialization rejects end of input

After whitespace, 228 reports `EofWhileParsingValue` through `peek_error`.
The scratch and depth are untouched. This is a concrete rejecting case,
with no assumed parser specification.
-/

namespace WNear.Binary.SerdeRej

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeStructArr (tbl roomS)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- 228 rejects a reader whose remaining bytes are all whitespace. -/
theorem f228_eof (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 336 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hr : roomFor4 mlen maxP 20) (heof : i + wsLen (bs.drop i) = bs.length) :
    endCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de))
        (fun _ => (500 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + costErr cfg F (bs.length + 1))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ tabs n de ∗
          rd n de ptr bs bs.length ∗ errRes n maxP out de live)) := by
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
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 64 + 8).toNat = (sp - 64).toNat + 8 := by
    simp [UInt32.toNat_add]; omega
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
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hd, Ht⟩
  subst hargs
  icases stk_split n (sp.toNat - 336) 192 144 $$ Hs with ⟨S192, S144⟩
  icases stk_split n (sp.toNat - 336 + 192) 80 64 $$ S144 with ⟨S80, F64⟩
  rw [show sp.toNat - 336 + 192 + 80 = (sp - 64).toNat by omega,
    show sp.toNat - 336 + 192 = (sp - 64).toNat - 80 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨B0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 12 44 $$ F56 with ⟨B8, B20⟩
  iunfold stk at B8
  icases B8 with ⟨%b12, %hb12, B8⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 8) 4 b12 (by omega) $$ B8 with ⟨B8, B12⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
  simp only [f228]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall s339 using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [B8]
  ihave C := U128From.memBytes_join n ((sp - 64).toNat + 8) 4 (bytes32 5) (b12.drop 4) (by simp) $$ [B8 B12]
  · iframe B8 B12
  have s322 := SerdeErrBox.f322_spec (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) de (sp - 64 + 8) ptr idx (bytes32 5 ++ b12.drop 4) bs bs.length
    maxP mlen live F (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hr
  rw [hE, h8] at s322
  ihave #S322 := s322 $$ [Hcode F640]
  · iframe Hcode F640
  clear s322
  mstep; mstep; mstep; mstep; mstep
  mcall S322 using [Hg S80 Hvt Hh C Hrd]
  · iframe Hg S80 Hvt Hh C Hrd
  icases HQ with ⟨%e, %⟨hrs, he⟩, Hg, S80, Hvt, HE, C, Hrd⟩
  subst hrs
  mstep [O4]
  mstep; mstep; mstep
  mcredits (20 * cfg.regularOpCost + R)
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt Hd Hrd
  isplitl [S192 S80 B0 C B20]
  · ihave C := stk_intro $$ C
    rw [show (bytes32 5 ++ b12.drop 4).length = 12 by simp; omega]
    ihave F20 := stk_join n (sp - 64).toNat 8 12 $$ [B0 C]
    · iframe B0 C
    ihave F64 := stk_join n (sp - 64).toNat 20 44 $$ [F20 B20]
    · rw [show (sp - 64).toNat + 8 + 12 = (sp - 64).toNat + 20 by omega]
      iframe F20 B20
    ihave S144 := stk_join n ((sp - 64).toNat - 80) 80 64 $$ [S80 F64]
    · rw [show (sp - 64).toNat - 80 + 80 = (sp - 64).toNat by omega]
      iframe S80 F64
    ihave S144 := stk_addr (show (sp - 64).toNat - 80 = sp.toNat - 336 + 192 by omega) $$ S144
    iapply stk_join n (sp.toNat - 336) 192 144
    iframe S192 S144
  ihave Ht := tbl_tabs n de $$ Ht
  icases Ht with ⟨Ht, D12, D16⟩
  iframe Ht
  iunfold heapA at HE
  icases HE with ⟨HE, Eblock⟩
  iunfold SerdeErrBox.heapR at HE
  icases HE with ⟨%mlen', %hmem, Hh⟩
  iunfold errRes
  iexists e, (1 : UInt32), (0 : UInt32), ((ob.drop 4).drop 4), ((e.toNat, 20) :: live), mlen', (max F 1)
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  simp only [UInt32.reduceToNat]
  iframe O0 O4 O8 Hh D12 D16
  isplitr
  · ipureintro
    refine ⟨by simp; omega, Or.inl ⟨rfl, .cons _ (.refl live)⟩⟩
  iunfold scrBlk
  simp only [ite_true]
  iempintro

/-- The concrete EOF case discharges the rejecting 228 contract. -/
theorem rej228_eof (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType)
    (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (heof : wsLen bs = bs.length)
    (Cd : IProp GF) [Persistent Cd] (hc : Cd ⊢ endCode n maxP inst mi A) :
    Rej228 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP
      (fun F => (500 + 96 * wsLen bs) * cfg.regularOpCost + costErr cfg F (bs.length + 1)) Cd := by
  intro d sp out ob mlen F live hd hob hout hsp hal hr
  have hs := f228_eof (GF := GF) cfg lim d types[36]! rfl inst mi A n g ta hm hd Cg gt sp out de ptr idx
    out out out out ob bs 0 maxP mlen F live hob hout hlen hptr hde hsp (Nat.zero_le _) hr.1
    (by simpa using heof)
  simp only [List.drop_zero] at hs
  iintro #HC
  ihave #Hv := hc $$ HC
  ihave #S := hs $$ Hv
  clear hs
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
    (P := fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 out, .i32 out, .i32 out, .i32 out]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs 0 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ tabs n de ∗
          rd n de ptr bs bs.length ∗ errRes n maxP out de live)) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Hs, Hvt, Hh, Ho, Hrd, Hd, Ht, Hkey⟩
    iframe Hg Hs Hvt Hh Ho Hrd Hd Ht Hkey
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨Hkey, %hrs, Hg, Hs, Hvt, Hd, Ht, Hrd, HE⟩
    iframe Hg Hs Hvt Hd Ht Hkey HE
    isplitr
    · ipureintro; exact hrs
    iexists bs.length
    iexact Hrd
  iexact S

end Proof

end WNear.Binary.SerdeRej
