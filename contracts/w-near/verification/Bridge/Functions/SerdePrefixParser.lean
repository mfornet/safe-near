import Bridge.Functions.SerdePrefixObject
import Bridge.Functions.SerdeObjectParserPrecise

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxHeartbeats 32000000 in
theorem f66_prefix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 44 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hrd : rd.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 432 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : KeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K646)
    (hkeysSaved : KeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K169)
    (hignored : IgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K81)
    (hignoredSaved : IgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 432) 432 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => (975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 432) 432 ∗
          vt n 1057464 idx ta (A 578) ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanLedgerObject n mlen F live a.val.toUTF8.toList p c len)) := by
  iintro ⟨#Hc66, #HC, #HP, #Hdrop, #HIgn⟩
  ihave #Hc66' := Hc66
  iunfold code66 at Hc66'
  icases Hc66' with ⟨#H193c, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77, #F214, #F91, #F228,
    #F78, #F634, #F320, #F68, #F747, #F778⟩
  ihave #Hv := H193c
  iunfold SerdeNextKey.code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  ihave #Hv' := Hv
  iunfold SerdeEnds.endCode at Hv'
  icases Hv' with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
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
  have hvalue : validAccountIdBytes a.val.toUTF8.toList = true := a.toNear.property
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalue
  have hpos : 0 < a.val.toUTF8.toList.length := by omega
  have hbytes : a.val.toUTF8.toList.length < 2 ^ 32 := by omega
  have hkl : k ≤ bs.length := by omega
  generalize hCS : SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0 = CS
  rw [Nat.add_mul]
  generalize hW : 96 * wsLen (bs.drop k) * cfg.regularOpCost = W
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hsr, Hbs, He, Hw, Hhex, Hkey, Hident⟩
  subst hargs
  -- the frame
  icases stk_split n (sp.toNat - 432) 368 64 $$ Hs with ⟨S368, F64⟩
  rw [show sp.toNat - 432 + 368 = (sp - 64).toNat by omega, show sp.toNat - 432 = (sp - 64).toNat - 368 by omega]
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
  ihave Hsb := SerdeScratchValueDrop.empty_scratch n 2048 mlen live F $$ Hh
  ihave Hscratch : SerdeValueState.scratchPre n 2048 mlen live F (sp - 64) 1 0 0 $$ [D20 D12 D16 Hsb]
  · iunfold SerdeValueState.scratchPre
    iframe D20 D12 D16 Hsb
  ihave Htables : SerdeValueState.tables n $$ [He Hw Hhex]
  · iunfold SerdeValueState.tables
    iframe He Hw Hhex
  have s78 := f78_prefix_cost (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) (sp - 64 + 48) (sp - 64) ptr idx ob2 bs 0 live iprop(emp) mlen F 1 0 K646 K169 K81
    hob2 (by omega) hlen hptr (by omega) (by omega) (by rw [h64]; omega) (by omega)
    hsetup (by simpa only [List.drop_zero, Nat.zero_add] using hkeys) (by simpa only [List.drop_zero, Nat.zero_add] using hkeysSaved) (by simpa only [List.drop_zero, Nat.zero_add] using hvalues) (by simpa only [List.drop_zero, Nat.zero_add] using hignored) (by simpa only [List.drop_zero, Nat.zero_add] using hignoredSaved) N a rest (by simpa using ho) (by simpa using hloop)
  rw [h48, hCS, ← hk] at s78
  ihave #Hobj : SerdeStructObjModelState.code n 2048 inst mi A $$ [H193c HP HC F205 F201 F193 F89 F90 F81 F169 F77]
  · iunfold SerdeStructObjModelState.code
    iframe H193c HP HC F205 F201 F193 F89 F90 F81 F169 F77
  ihave #S78 := s78 $$ [Hobj HIgn F228 Hi]
  · iframe Hobj HIgn F228 Hi
  clear s78
  mstep; mstep; mstep; mstep
  mcall S78 using [Hg S368 OB Hrd D24 Hvt Htables Hkey Hident Hscratch]
  · iframe Hg S368 OB Hrd D24 Hvt Htables Hkey Hident Hscratch
  icases HQ with ⟨%hrs, Hg, S368, D24, %p, %cap, W0, W4, W8, W12, %hp, Hmember, Hrd⟩
  let l := UInt32.ofNat a.val.utf8ByteSize
  iunfold WNear.Binary.SerdeStructObjKeyState.member at Hmember
  icases Hmember with ⟨%⟨hcap, _⟩, Hbytes, Hcore⟩
  iunfold WNear.Binary.SerdeStructObjKeyState.core at Hcore
  icases Hcore with ⟨%hl1, %F1, %scratch, %capS, %slFinal, %⟨hb, _⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  obtain ⟨hlo, hhi, hF1⟩ := Ledger.final_bounds bs mlen F k hl1 F1 true capS hlen hb
  subst hrs
  mcredits (865 * cfg.regularOpCost + W + R)
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
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨He, Hw, Hhex⟩
  icases stk_split n ((sp - 64).toNat - 368) 272 96 $$ S368 with ⟨S272, S96⟩
  rw [show (sp - 64).toNat - 368 + 272 = (sp - 64).toNat - 96 by omega]
  have s320 := SerdeEndSuccess.f320_eof (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) (sp - 64) ptr bs k (by omega) (by omega) (by omega) hkl hend
  rw [Nat.add_mul, hW] at s320
  ihave #S320 := s320 $$ [F332 F333 F339 Hi]
  · iframe F332 F333 F339 Hi
  clear s320
  mstep
  mcall S320 using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  mcredits (631 * cfg.regularOpCost + R)
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep [A32]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [Q4]
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep [Q0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [A40]
  mstep [Q12]
  have s68 := f68_retained_scratch (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm
    (by omega) Cg 2048 hl1 ((p.toNat, cap.toNat) :: live) F1 (sp - 64) scratch capS slFinal (by omega)
  ihave #S68 := s68 $$ Hdrop
  clear s68
  mstep; mstep; mstep
  mcall S68 using [Hscratch]
  · isplitr
    · ipureintro; trivial
    · iexact Hscratch
  icases HQ with ⟨%hrs, D12, D16, D20, Hheap⟩
  subst hrs
  ihave Hheap := AllocInv.heapInv_mono n 2048 hl1 ((p.toNat, cap.toNat) :: live) (F1 + 1) (F + 43)
    (by omega) $$ Hheap
  ihave Hclean : cleanLedgerObject n mlen F live a.val.toUTF8.toList p cap l $$ [Hbytes Hheap]
  · iunfold cleanLedgerObject
    isplitr
    · ipureintro
      have hs := SerdeAcctHyp.utf8_len a.val
      exact ⟨by rw [hcap, hs], by dsimp [l]; rw [hs], hp⟩
    iframe Hbytes
    iexists hl1
    iframe Hheap
    ipureintro; exact ⟨hlo, hhi⟩
  mcredits (5 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  iframe He Hw Hhex Hkey Hident
  iunfold SerdeRead.rd at Hrd
  icases Hrd with ⟨Dsr, Hbs⟩
  iframe Hbs
  ihave R := KeyGet.split64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ R
  icases R with ⟨R0, R4⟩
  isplitl [S272 S96 Dsr D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W12]
  · iunfold sliceRead at Dsr
    icases Dsr with ⟨G0, G4, G8⟩
    ihave S368 := stk_join n ((sp - 64).toNat - 368) 272 96 $$ [S272 S96]
    · rw [show (sp - 64).toNat - 368 + 272 = (sp - 64).toNat - 96 by omega]; iframe S272 S96
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
    ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 368 + 368 by omega) $$ F64
    iapply stk_join n ((sp - 64).toNat - 368) 368 64
    iframe S368 F64
  isplitl [R0 R4 R8]
  · iunfold sliceRead
    iframe R0 R4 R8
  iexists p, cap, l
  ihave Q4 := KeyGet.split64 n (out.toNat + 4) p cap $$ Q4
  icases Q4 with ⟨Q4, Q8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe Q0 Q4 Q8 Q12 Hclean


end Resource
end WNear.Binary.SerdeObjectPrefix

namespace WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeStructObjKeyState (member)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeValueState (scratchPre)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
theorem f65_prefix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 45 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out ptr idx : UInt32) (ob bs : List UInt8) (a : WNear.AccountId)
    (rest : List UInt8) (N k : Nat) (mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 448 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (K646 K169 K81 : Nat → Nat)
    (hsetup : LedgerSetup mlen F)
    (hkeys : KeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K646)
    (hkeysSaved : KeyGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K646)
    (hvalues : ValueGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K169)
    (hignored : IgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F false) K81)
    (hignoredSaved : IgnoreGasCharges cfg bs (Bound bs (wsLen bs + 1) mlen F true) K81)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hk : k = bs.length - rest.length) (hend : k + wsLen (bs.drop k) = bs.length) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f65 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n 2048 mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => 45 * cfg.regularOpCost + ((975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanLedgerObject n mlen F live a.val.toUTF8.toList p c len)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  let P : IProp GF := iprop(stk n (sp.toNat - 448) 432 ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n 2048 mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
    n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes)
  let Q : List Value → IProp GF := fun _ => iprop(stk n (sp.toNat - 448) 432 ∗ vt n 1057464 idx ta (A 578) ∗
    n ↦[wms][ ptr.toNat ] bs ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
    n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
    n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
    ∃ (p c len : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
      n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] len ∗
      cleanLedgerObject n mlen F live a.val.toUTF8.toList p c len)
  let K := (975 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost + SerdeStructObj.costObj cfg (K646) (K169) (K81) (valueAs WNear.account) SerdeIgnObject.ignored bs N 0
  have hs := f66_prefix (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 16) out (sp - 16) ptr idx ob bs a rest N k mlen F live hob hout
    (by omega) hlen hptr (by omega) (by rw [h16]; omega) K646 K169 K81 hsetup hkeys hkeysSaved hvalues hignored hignoredSaved ho hloop hk hend
  rw [show (sp - 16).toNat - 432 = sp.toNat - 448 by omega] at hs
  have hs' : code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗
      ParseStr.code646 n 2048 inst mi A ∗ DropVec.dropCode inst mi A ∗ SerdeIgnMember.code n 2048 inst mi A ⊢
      MFunSpec cfg lim (d + 1) types[14]! inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 (sp - 16)]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          sliceRead n (sp - 16) ptr (UInt32.ofNat bs.length) 0 ∗ P))
        (fun _ => K)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          (∃ a b c : UInt32, sliceRead n (sp - 16) a b c) ∗ Q rs)) := by
    apply hs.trans
    apply SerdeValueState.spec_repack
    · intro args
      dsimp only [P]
      iintro ⟨%ha, Hg, Hrd, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, Hkey, Hident⟩
      iframe Hg Hs Hvt Hheap Ho Hrd Hbs He Hw Hhex Hkey Hident
      ipureintro; exact ha
    · intro args rs
      dsimp only [Q]
      iintro ⟨%hrs, Hg, Hs, Hvt, Hrd, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
      iframe Hg Hs Hvt Hbs He Hw Hhex Hkey Hident Hresult
      isplitr
      · ipureintro; exact hrs
      iexists ptr, UInt32.ofNat bs.length, 0
      iexact Hrd
  have key := ArgsLeaves.f65_of_66 (GF := GF) cfg lim d type htype inst mi n g hm.mem hm.glob (A 66) (A 644)
    (hm.funcs 66 (by decide)) (hm.funcs 644 (by decide)) (by omega) Cg gt sp out ptr (UInt32.ofNat bs.length)
    (by omega) P K Q
  iintro ⟨#H66, #HC, #HP, #HD, #HIgn, #F644, #F66, #Hi⟩
  ihave #S66 := hs' $$ [H66 HC HP HD HIgn]
  · iframe H66 HC HP HD HIgn
  ihave #S65 := key $$ [F644 F66 Hi S66]
  · iframe F644 F66 Hi S66
  iapply SerdeValueState.spec_repack ?hPre ?hPost $$ S65
  case hPre =>
    intro args
    dsimp only [P]
    iintro ⟨%ha, Hg, Hs, Hvt, Hheap, Ho, Hbs, He, Hw, Hhex, Hkey, Hident⟩
    icases stk_split n (sp.toNat - 448) 432 16 $$ Hs with ⟨Hs, Hs16⟩
    ihave Hs16 := stk_addr (show sp.toNat - 448 + 432 = sp.toNat - 16 by omega) $$ Hs16
    iframe Hg Hs16 Hs Hvt Hheap Ho Hbs He Hw Hhex Hkey Hident
    ipureintro; exact ha
  case hPost =>
    intro args rs
    dsimp only [Q]
    iintro ⟨%hrs, Hg, Hs16, Hs, Hvt, Hbs, He, Hw, Hhex, Hkey, Hident, Hresult⟩
    iframe Hg Hvt Hbs He Hw Hhex Hkey Hident Hresult
    isplitr
    · ipureintro; exact hrs
    ihave Hs16 := stk_addr (show sp.toNat - 16 = sp.toNat - 448 + 432 by omega) $$ Hs16
    iapply stk_join n (sp.toNat - 448) 432 16
    iframe Hs Hs16



end Resource
end WNear.Binary.SerdeObjectPrefix
