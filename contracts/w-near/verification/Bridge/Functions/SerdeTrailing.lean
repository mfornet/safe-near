import Bridge.Functions.SerdeFromReject
import Bridge.Functions.AllocFinite
import Bridge.Functions.ToVec

/-!
# Rejecting trailing non-whitespace after a parsed struct

The account string is dropped, the syntax-error box is propagated, and the
scratch is dropped before 66 returns. The cost is finite and independent of
the gas ceiling, using the heap's physical free-list bound for the error box.
-/

namespace WNear.Binary.SerdeRej

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode)
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169 roomS)
open WNear.Binary.SerdeStructObj (Hyp646 Hyp81)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 i64_one frame66)
open NearInterface.Json

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- 66 rejects non-whitespace after a successfully parsed struct. -/
theorem f66_trailing (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hsp : 400 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hr : roomS mlen maxP)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat) (Fb : Nat) (Cd : IProp GF) [Persistent Cd]
    (h646 : Hyp646 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP K646 Cd)
    (h169 : Hyp169 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP dv K169 Fb Cd)
    (h81 : Hyp81 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP ign K81 Cd) (hF : F ≤ Fb)
    (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (higns : ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r)
    (hstrs : ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r)
    (a : WNear.AccountId) (r : List UInt8)
    (hS : SerdeStructModel.structDe "account_id" dv ign bs = some (a, r)) (hE : skipWhitespace r ≠ [])
    (hsuf : bs.drop (bs.length - r.length) = r) :
    code66 n maxP inst mi A ∗ DropVec.dropCode inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗
          sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => (2000 + 96 * r.length) * cfg.regularOpCost + SerdeStruct78.costS cfg K646 K169 K81 dv ign bs +
          costErr cfg (2 ^ 32) (bs.length + 1))
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
  have hrl : r.length ≤ bs.length := by
    have := congrArg List.length hsuf; simp at this; omega
  have hwr : wsLen (bs.drop (bs.length - r.length)) = wsLen r := by rw [hsuf]
  have hwle := SerdeRead.wsLen_le r
  have hbad : bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) ≠ bs.length := by
    intro he
    apply hE
    have hw : wsLen r = r.length := by omega
    rw [SerdeRead.skipWhitespace_eq r, hw]
    simp
  generalize hCS : SerdeStruct78.costS cfg K646 K169 K81 dv ign bs = CS
  rw [Nat.add_mul]
  generalize hW : 96 * r.length * cfg.regularOpCost = W
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
  have s78 := SerdeStruct78.f78_acc (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt (sp - 64) (sp - 64 + 48) (sp - 64) ptr idx ob2 bs maxP mlen F live hob2 (by omega) hlen hptr (by omega)
    (by omega) (by omega) hr dv ign K646 K169 K81 Fb Cd h646 h169 h81 hF hdv0 hdvs higns hstrs a r hS
  rw [h48, hCS] at s78
  ihave #S78 := s78 $$ [H193c F205 F201 F193 F89 F90 F81 F169 F77 F214 F91 F228 HCd]
  · iframe H193c F205 F201 F193 F89 F90 F81 F169 F77 F214 F91 F228 HCd
  clear s78
  mstep; mstep; mstep; mstep
  mcall S78 using [Hg S336 Hvt Hh OB Hrd D24 Ht Hkey]
  · iframe Hg S336 Hvt Hh OB Hrd D24 Ht Hkey
  icases HQ with ⟨%hrs, Hg, S336, Hvt, D24, Ht, Hkey, %p, %cap, W0, W4, W8, W12, Hstr, Hrd⟩
  subst hrs
  iunfold stk at A32 A40
  icases A32 with ⟨%a32, %ha32, A32⟩
  icases A40 with ⟨%a40, %ha40, A40⟩
  rw [show (sp - 64).toNat + 48 + 12 = (sp - 64).toNat + 60 by omega,
    show (sp - 64).toNat + 48 + 8 = (sp - 64).toNat + 56 by omega,
    show (sp - 64).toNat + 48 + 4 = (sp - 64).toNat + 52 by omega]
  mstep; mstep; mstep; mstep
  mstep; mstep [W0]; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep [W12]
  mstep [A40]
  ihave W52 := KeyGet.join64 n ((sp - 64).toNat + 52) p cap $$ [W4 W8]
  · rw [show (sp - 64).toNat + 52 + 4 = (sp - 64).toNat + 56 by omega]; iframe W4 W8
  mstep; mstep
  mstep [W52]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [A32]
  rw [VecFromElem.storeBytes_pair64]
  iunfold strRes at Hstr
  icases Hstr with ⟨%mlen', %F', %⟨hp', hcap, hr'⟩, Hbytes, Hblk, Hh⟩
  icases stk_split n ((sp - 64).toNat - 336) 240 96 $$ S336 with ⟨S240, S96⟩
  rw [show (sp - 64).toNat - 336 + 240 = (sp - 64).toNat - 96 by omega]
  ihave Hh := heapInv_finite n maxP mlen' ((p.toNat, cap.toNat) :: live) F' $$ Hh
  have s320 := SerdeEnds.f320_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 64) (sp - 64) ptr idx bs (bs.length - r.length) maxP mlen' ((p.toNat, cap.toNat) :: live) (2 ^ 32) hlen hptr
    (by omega) (by omega) (by omega) hr'
  have hcost : SerdeEnds.costEnd cfg (2 ^ 32) 200 (wsLen (bs.drop (bs.length - r.length)))
      (bs.length - r.length + wsLen (bs.drop (bs.length - r.length)))
      (bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) = bs.length) ≤
      (220 + 96 * r.length) * cfg.regularOpCost + costErr cfg (2 ^ 32) (bs.length + 1) := by
    have hj : bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) ≤ bs.length := by omega
    have hm := SerdeEndSeq.costErr_mono cfg (2 ^ 32) (bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) + 1)
      (bs.length + 1) (by omega)
    unfold SerdeEnds.costEnd
    rw [if_neg hbad]
    have := Nat.mul_le_mul_right cfg.regularOpCost (show 200 + 96 * wsLen (bs.drop (bs.length - r.length)) ≤ 200 + 96 * r.length by omega)
    simp only [Nat.add_mul] at *
    omega
  simp only [Nat.reducePow, Nat.add_mul, hW] at hcost
  generalize hEE : costErr cfg (2 ^ 32) (bs.length + 1) = EE at hcost ⊢
  ihave #S320 := s320 $$ Hv
  clear s320
  mstep
  mcall S320 using [Hg S96 Hvt Hh Hrd]
  · iframe Hg S96 Hvt Hh Hrd
  icases HQ with ⟨Hg, S96, Hvt, HQ⟩
  ihave HQ := SerdeValueSeed.resEnd_neg hbad $$ HQ
  icases HQ with ⟨%e, %⟨hrs, he⟩, HE, Hrd⟩
  subst hrs
  mstep; mstep
  mstep_not_taken with simp [Numeric.bool, he]
  icases U128From.memBytes_split n (out.toNat + 4) 4 ((ob.drop 4).take 8) (by simp; omega) $$ Q4 with ⟨Q4, Q8⟩
  mstep; mstep; mstep [Q0]
  mstep; mstep; mstep [Q4]
  iunfold heapA at HE
  icases HE with ⟨HE, Eblock⟩
  iunfold SerdeErrBox.heapR at HE
  icases HE with ⟨%mlen'', %hmem, Hh⟩
  ihave Ab := KeyGet.split64 n ((sp - 64).toNat + 32) p cap $$ A32
  icases Ab with ⟨A32, A36⟩
  rw [show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega]
  have hab : a.val.toUTF8.toList.length = a.val.utf8ByteSize := by
    rw [String.toUTF8_eq_toByteArray, ToVec.toList_eq]
    simp [String.size_toByteArray]
  ihave Ab : block n p.toNat cap.toNat $$ [Hbytes Hblk]
  · iunfold block at Hblk
    icases Hblk with ⟨%rest, %hrest, Hblk⟩
    ihave Hb := U128From.memBytes_join n p.toNat a.val.utf8ByteSize a.val.toUTF8.toList rest hab $$ [Hbytes Hblk]
    · iframe Hbytes Hblk
    iunfold block
    iexists a.val.toUTF8.toList ++ rest
    iframe Hb
    ipureintro; simp only [List.length_append, hab]; omega
  have hscr : scrOk ((e.toNat, 20) :: live)
      ((e.toNat, 20) :: (p.toNat, cap.toNat) :: live) p cap := by
    by_cases hc : cap = 0
    · exact Or.inl ⟨hc, .cons₂ _ (.cons _ (.refl live))⟩
    · right
      refine ⟨hc, by simp, ?_⟩
      have herase : (((e.toNat, 20) :: (p.toNat, cap.toNat) :: live).erase (p.toNat, cap.toNat)) =
          (e.toNat, 20) :: live := by
        by_cases heq : (e.toNat, 20) = (p.toNat, cap.toNat)
        · rw [heq]; simp
        · simp [heq]
      rw [herase]
  ihave Ab : scrBlk n p cap $$ [Ab]
  · iunfold scrBlk
    split
    · iempintro
    · iexact Ab
  have h32 : (sp - 64 + 32).toNat = (sp - 64).toNat + 32 := by
    simp [UInt32.toNat_add]; omega
  have s68a := f68_scratch (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega)
    Cg maxP mlen'' ((e.toNat, 20) :: live) ((e.toNat, 20) :: (p.toNat, cap.toNat) :: live)
    (max (2 ^ 32) 1) (sp - 64 + 32) p cap (UInt32.ofNat a.val.utf8ByteSize) hscr (by rw [h32]; omega)
  ihave #S68a := s68a $$ HD
  clear s68a
  mstep; mstep; mstep
  mcall S68a using [A32 A36 A40 Hh Ab]
  · iunfold scratchPre
    rw [show (sp - 64 + 32).toNat = (sp - 64).toNat + 32 by simp [UInt32.toNat_add]; omega,
      show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega,
      show (sp - 64).toNat + 32 + 8 = (sp - 64).toNat + 40 by omega]
    iframe A32 A36 A40 Hh Ab
    ipureintro; rfl
  iunfold scratchPost at HQ
  rw [show (sp - 64 + 32).toNat = (sp - 64).toNat + 32 by simp [UInt32.toNat_add]; omega,
    show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega,
    show (sp - 64).toNat + 32 + 8 = (sp - 64).toNat + 40 by omega]
  icases HQ with ⟨%hrs, A32, A36, A40, %live', %F'', %hsub, Hh⟩
  subst hrs
  iunfold tbl at Ht
  icases Ht with ⟨Hsl, He, Hw, D12, D16, Hid⟩
  rw [show (sp - 64).toNat + 16 = (sp - 64).toNat + 12 + 4 by omega]
  have s68 := SerdeFromTrait.f68_zero (GF := GF) cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg
    (sp - 64 + 12) (by omega)
  rw [h12] at s68
  ihave #S68 := s68 $$ [Hi F747 F778]
  · iframe Hi F747 F778
  clear s68
  mstep; mstep; mstep
  mcall S68 using [D16]
  · iframe D16
  icases HQ with ⟨%hrs, D16⟩
  subst hrs
  mcredits (20 * cfg.regularOpCost + R)
  mstep
  mstep; mstep; mstep
  rw [show sp - 64 + 64 = sp by simp]
  mcredits (cfg.regularOpCost + R)
  iapply NearLogic.mwpi_global_set'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rfl
  isplitl [Hg]
  · iexact Hg
  isplitr
  · ipureintro; exact ⟨by omega, hg⟩
  inext
  iintro Hc Hg
  iapply NearLogic.mfunc_normal_intro'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; simp [htype]
  iintro Hc
  simp only [List.reverse_nil, List.length_nil, List.drop_nil]
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  ihave A32 := KeyGet.join64 n ((sp - 64).toNat + 32) p cap $$ [A32 A36]
  · rw [show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega]
    iframe A32 A36
  iframe Hg Hvt Hkey Hid
  icases Hsl with ⟨%sl, D20⟩
  iframe He Hw
  iunfold SerdeRead.rd at Hrd
  icases Hrd with ⟨Dsr, Hbs⟩
  iframe Hbs
  ihave R := KeyGet.split64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ R
  icases R with ⟨R0, R4⟩
  isplitl [S240 S96 Dsr D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W12]
  · iunfold sliceRead at Dsr
    icases Dsr with ⟨G0, G4, G8⟩
    ihave S336 := stk_join n ((sp - 64).toNat - 336) 240 96 $$ [S240 S96]
    · rw [show (sp - 64).toNat - 336 + 240 = (sp - 64).toNat - 96 by omega]; iframe S240 S96
    ihave W52 := KeyGet.split64 n ((sp - 64).toNat + 52) p cap $$ W52
    icases W52 with ⟨W52, W56⟩
    ihave G0 := stk_word $$ G0
    ihave G4 := stk_word $$ G4
    ihave G8 := stk_word $$ G8
    ihave D12 := stk_word $$ D12
    ihave D16 := stk_word $$ D16
    ihave D20 := stk_word $$ D20
    ihave D24 := stk_intro $$ D24
    ihave A32 := stk_intro $$ A32
    ihave A40 := stk_word $$ A40
    ihave W0 := stk_word $$ W0
    ihave W52 := stk_word $$ W52
    ihave W56 := stk_word $$ W56
    ihave W12 := stk_word $$ W12
    rw [show (bytes32 p ++ bytes32 cap).length = 8 by simp, show ([128] : List UInt8).length = 1 by rfl,
      show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 52 + 4 = (sp - 64).toNat + 56 by omega]
    ihave F64 := frame66 n (sp - 64).toNat $$ [G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W56 W12]
    · iframe G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W56 W12
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
  iexists e, (((ob.drop 4).take 8 |>.drop 4) ++ (ob.drop 4).drop 8), live', mlen'', F''
  iframe Q0 Q4 Q8 Hh
  ipureintro
  constructor
  · simp; omega
  · exact (List.Sublist.cons (e.toNat, 20) (.refl live)).trans hsub

end Proof

end WNear.Binary.SerdeRej
