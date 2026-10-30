import Bridge.Functions.SerdeScratchDrop

/-!
# `from_trait` propagates a rejected struct

This is the rejecting branch through `deserialize_struct` (228), conditional
on its specification. The scratch may have grown and is freed before returning.
The separate trailing-characters rejection after a successful struct is not
covered by this theorem.
-/

namespace WNear.Binary.SerdeRej

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeStructArr (tbl roomS)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 i64_one frame66)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- An error result after its scratch buffer has been freed. -/
def errOut (n maxP : Nat) (out : UInt32) (live : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (e : UInt32) (b8 : List UInt8) (live' : List (Nat × Nat)) (mlen F : Nat),
    ⌜b8.length = 8 ∧ live.Sublist live'⌝ ∗
    n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] e ∗ n ↦[wms][ out.toNat + 8 ] b8 ∗
    heapInv n maxP mlen live' F)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Struct deserialization fails: 66 returns its error and frees the scratch. -/
theorem f66_struct_rej (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hsp : 400 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hr : roomS mlen maxP)
    (K : Nat → Nat) (Cd : IProp GF) [Persistent Cd]
    (h228 : Rej228 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP K Cd) :
    code66 n maxP inst mi A ∗ DropVec.dropCode inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗
          sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 1000 * cfg.regularOpCost + K F)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗
          vt n 1057464 idx ta (A 578) ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
          n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
          errOut n maxP out live)) := by
  iintro ⟨#Hc66, #HD, #HCd⟩
  ihave #Hc66' := Hc66
  iunfold code66 at Hc66'
  icases Hc66' with ⟨#H193c, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77, #F214, #F91, #F228,
    #F78, #F634, #F320, #F68, #F747, #F778⟩
  ihave #Hv := H193c
  iunfold SerdeNextKey.code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  ihave #Hv' := Hv
  iunfold SerdeEnds.endCode at Hv'
  icases Hv' with ⟨#Hcode, -⟩
  iunfold SerdeErrBox.errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha634 := hm.funcs 634 (by decide)
  have ha78 := hm.funcs 78 (by decide)
  have ha320 := hm.funcs 320 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 64 + 48).toNat = (sp - 64).toNat + 48 := by simp [UInt32.toNat_add]; omega
  have h12 : (sp - 64 + 12).toNat = (sp - 64).toNat + 12 := by simp [UInt32.toNat_add]; omega
  generalize hCS : K F = CS
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hsr, Hbs, He, Hw, Hkey, Hid⟩
  subst hargs
  -- the frame
  icases stk_split n (sp.toNat - 400) 336 64 $$ Hs with ⟨S336, F64⟩
  rw [show sp.toNat - 400 + 336 = (sp - 64).toNat by omega, show sp.toNat - 400 = (sp - 64).toNat - 336 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨O0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 4 52 $$ F56 with ⟨O8, F52⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4) 8 44 $$ F52 with ⟨O12, F44⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8) 4 40 $$ F44 with ⟨O20, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4) 1 39 $$ F40 with ⟨O24, F39⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1) 7 32 $$ F39 with ⟨X25, F32⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7) 8 24 $$ F32 with ⟨A32, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8) 4 20 $$ F24 with ⟨A40, F20⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4) 4 16 $$ F20 with ⟨A44, F16⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4) 8 8 $$ F16 with ⟨B48, F8⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8) 4 4 $$ F8 with ⟨B56, B60⟩
  rw [show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8 + 4 = (sp - 64).toNat + 60 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8 = (sp - 64).toNat + 56 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 = (sp - 64).toNat + 48 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 = (sp - 64).toNat + 44 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 = (sp - 64).toNat + 32 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 = (sp - 64).toNat + 25 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 = (sp - 64).toNat + 24 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 = (sp - 64).toNat + 20 by omega,
    show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega]
  iunfold stk at O0 O8 O12 O20 O24 B48 B56
  icases O0 with ⟨%o0, %ho0, O0⟩
  icases O8 with ⟨%o8, %ho8, O8⟩
  icases O12 with ⟨%o12, %ho12, O12⟩
  icases O20 with ⟨%o20, %ho20, O20⟩
  icases O24 with ⟨%o24, %ho24, O24⟩
  icases B48 with ⟨%b48, %hb48, B48⟩
  icases B56 with ⟨%b56, %hb56, B56⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Q0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨Q4, Q12⟩
  rw [show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  iunfold sliceRead at Hsr
  icases Hsr with ⟨R0, R4, R8⟩
  ihave R := KeyGet.join64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ [R0 R4]
  · iframe R0 R4
  simp only [f66]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [R8]
  mstep [B56]
  mstep; mstep
  mstep [R]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [B48]
  rw [VecFromElem.storeBytes_pair64]
  ihave B48 := KeyGet.split64 n ((sp - 64).toNat + 48) ptr (UInt32.ofNat bs.length) $$ B48
  icases B48 with ⟨B48, B52⟩
  have s634 := ArgsLeaves.f634_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 64)
    (sp - 64 + 48) ptr (UInt32.ofNat bs.length) 0 o0 o8 o12 o20 o24 ho0 ho8 ho12 ho20 ho24 (by omega) (by omega)
  mstep; mstep; mstep; mstep
  mcall s634 using [B48 B52 B56 O0 O8 O12 O20 O24]
  · iunfold sliceRead
    rw [h48]
    iframe B48 B52 B56 O0 O8 O12 O20 O24
  icases HQ with ⟨%hrs, Hsl, HD⟩
  subst hrs
  clear s634
  iunfold sliceRead at Hsl
  rw [h48]
  icases Hsl with ⟨B48, B52, B56⟩
  ihave B48 := stk_word $$ B48
  ihave B52 := stk_word $$ B52
  ihave B56 := stk_word $$ B56
  ihave OB := stk_join n _ 4 4 $$ [B48 B52]
  · iframe B48 B52
  ihave OB := stk_join n _ 8 4 $$ [OB B56]
  · iframe OB B56
  ihave OB := stk_join n _ 12 4 $$ [OB B60]
  · iframe OB B60
  iunfold stk at OB
  icases OB with ⟨%ob2, %hob2, OB⟩
  iunfold deserializer at HD
  icases HD with ⟨Dsr, D12, D20, D24⟩
  ihave Hrd : SerdeRead.rd n (sp - 64) ptr bs 0 $$ [Dsr Hbs]
  · iunfold SerdeRead.rd
    iframe Hbs
    iexact Dsr
  rw [i64_one]
  ihave D12 := KeyGet.split64 n ((sp - 64).toNat + 12) 1 0 $$ D12
  icases D12 with ⟨D12, D16⟩
  rw [show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega]
  ihave Ht : tbl n (sp - 64) $$ [D20 He Hw D12 D16 Hid]
  · iunfold tbl
    iframe He Hw D12 D16 Hid
    iexists 0
    iexact D20
  have s78 := f78_rej (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg
    gt (sp - 64) (sp - 64 + 48) (sp - 64) ptr idx ob2 bs maxP mlen F live hob2 (by omega)
    (by omega) (by omega) hr K Cd h228
  rw [h48, hCS] at s78
  ihave #S78 := s78 $$ [Hi F228 HCd]
  · iframe Hi F228 HCd
  clear s78
  mstep; mstep; mstep; mstep
  mcall S78 using [Hg S336 Hvt Hh OB Hrd D24 Ht Hkey]
  · iframe Hg S336 Hvt Hh OB Hrd D24 Ht Hkey
  icases HQ with ⟨%hrs, Hg, S336, Hvt, D24, Ht, Hkey, HR, HE⟩
  subst hrs
  iunfold errRes at HE
  icases HE with ⟨%e, %p, %c, %b8, %live', %mlen', %F', %⟨hb8, hscr⟩, W0, W4, W8, Hh, D12, D16, Hb⟩
  rw [h48, show (sp - 64).toNat + 48 + 4 = (sp - 64).toNat + 52 by omega,
    show (sp - 64).toNat + 48 + 8 = (sp - 64).toNat + 56 by omega]
  icases U128From.memBytes_split n (out.toNat + 4) 4 ((ob.drop 4).take 8) (by simp; omega) $$ Q4 with ⟨Q4, Q8⟩
  mstep; mstep; mstep; mstep
  mstep; mstep [W0]; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [W4]; mstep [Q4]
  mstep; mstep; mstep [Q0]
  mstep
  iunfold tabs at Ht
  icases Ht with ⟨⟨%sl, D20⟩, He, Hw, Hid⟩
  have s68 := f68_scratch (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega)
    Cg maxP mlen' live live' F' (sp - 64 + 12) p c sl hscr (by omega)
  ihave #S68 := s68 $$ HD
  clear s68
  mstep; mstep; mstep
  mcall S68 using [D12 D16 D20 Hh Hb]
  · iunfold scratchPre
    rw [h12, show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 12 + 8 = (sp - 64).toNat + 20 by omega]
    iframe D12 D16 D20 Hh Hb
    ipureintro; rfl
  iunfold scratchPost at HQ
  rw [h12, show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega,
    show (sp - 64).toNat + 12 + 8 = (sp - 64).toNat + 20 by omega]
  icases HQ with ⟨%hrs, D12, D16, D20, %live'', %F'', %hsub, Hh⟩
  subst hrs
  mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt Hkey Hid He Hw
  icases HR with ⟨%j, Hrd⟩
  iunfold SerdeRead.rd at Hrd
  icases Hrd with ⟨Dsr, Hbs⟩
  iframe Hbs
  ihave R := KeyGet.split64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ R
  icases R with ⟨R0, R4⟩
  isplitl [S336 Dsr D12 D16 D20 D24 X25 A32 A40 A44 W0 W4 W8]
  · iunfold sliceRead at Dsr
    icases Dsr with ⟨G0, G4, G8⟩
    icases U128From.memBytes_split n ((sp - 64).toNat + 56) 4 b8 (by omega) $$ W8 with ⟨W56, W60⟩
    ihave G0 := stk_word $$ G0
    ihave G4 := stk_word $$ G4
    ihave G8 := stk_word $$ G8
    ihave D12 := stk_word $$ D12
    ihave D16 := stk_word $$ D16
    ihave D20 := stk_word $$ D20
    ihave D24 := stk_intro $$ D24
    ihave W0 := stk_word $$ W0
    ihave W4 := stk_word $$ W4
    ihave W56 := stk_intro $$ W56
    ihave W60 := stk_intro $$ W60
    rw [show ([128] : List UInt8).length = 1 by rfl,
      show (List.take 4 b8).length = 4 by simp; omega,
      show (List.drop 4 b8).length = 4 by simp; omega,
      show (sp - 64).toNat + 56 + 4 = (sp - 64).toNat + 60 by omega]
    ihave F64 := frame66 n (sp - 64).toNat $$ [G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W4 W56 W60]
    · iframe G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W4 W56 W60
    ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 336 + 336 by omega) $$ F64
    iapply stk_join n ((sp - 64).toNat - 336) 336 64
    iframe S336 F64
  isplitl [R0 R4 R8]
  · iunfold sliceRead
    iframe R0 R4 R8
  iunfold errOut
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  have hq8 : ((ob.drop 4).take 8 |>.drop 4).length = 4 := by simp; omega
  ihave Q8 := U128From.memBytes_join n (out.toNat + 8) 4 ((ob.drop 4).take 8 |>.drop 4)
    ((ob.drop 4).drop 8) hq8 $$ [Q8 Q12]
  · rw [show out.toNat + 8 + 4 = out.toNat + 12 by omega]
    iframe Q8 Q12
  iexists e, (((ob.drop 4).take 8 |>.drop 4) ++ (ob.drop 4).drop 8), live'', mlen', F''
  iframe Q0 Q4 Q8 Hh
  ipureintro
  constructor
  · simp; omega
  · exact hsub

end Proof

end WNear.Binary.SerdeRej
