import Bridge.Functions.SerdeFromTrait
import Bridge.Functions.SerdeStruct78Esc
import Bridge.Functions.SerdeScratchValueDrop
import Bridge.Functions.SerdeEndSuccess

/-!
# from_trait on an array containing a copied account-id value

The real entry constructs its empty deserializer, executes 78/228, checks the
remaining whitespace, copies the owned result, and frees grown scratch. Both
memory growth and allocator bounds survive cleanup.
-/

namespace WNear.Binary.SerdeFromTraitEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeFromTrait (code66 frame66 i64_one)
open WNear.Binary.SerdeStruct78Esc (costArray)
open WNear.Binary.SerdeValueState (scratchPre)
open WNear.Binary.SerdeScratchValueDrop (cleanValue)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The actual 66 call accepts an escaped account-id array and frees its grown scratch. -/
theorem f66_arr_copied (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 37 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8) (value : String)
    (rest : List UInt8) (j k : Nat) (maxP mlen F : Nat) (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hrd : rd.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hsp : 432 ≤ sp.toNat)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1))) (hroom : roomRun maxP mlen 0 [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (halloc : roomFor (mlen + growthPages 0 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    code66 n maxP inst mi A ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A ∗ DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 432) 432 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg F 0 bs value.toUTF8.toList rest j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 432) 432 ∗
          vt n 1057464 idx ta (A 578) ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ cleanValue n maxP mlen live F 0 bs value.toUTF8.toList (j + 1) p c len)) := by
  iintro ⟨#Hc66, #HC, #HP, #Hdrop⟩
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
  have hvalue := hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalue
  have hpos : 0 < value.toUTF8.toList.length := by omega
  have hbytes : value.toUTF8.toList.length < 2 ^ 32 := by omega
  have hkl : k ≤ bs.length := by
    have hb := SerdeNextKey.getElem_lt he
    rw [hk]
    omega
  generalize hCS : costArray cfg F 0 bs value.toUTF8.toList rest j = CS
  rw [Nat.add_mul]
  generalize hW : 96 * wsLen (bs.drop k) * cfg.regularOpCost = W
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hsr, Hbs, He, Hw, Hhex⟩
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
  ihave Hsb := SerdeScratchValueDrop.empty_scratch n maxP mlen live F $$ Hh
  ihave Hstate : iprop(scratchPre n maxP mlen live F (sp - 64) 1 0 0 ∗ SerdeValueState.tables n)
      $$ [D20 D12 D16 Hsb He Hw Hhex]
  · iunfold scratchPre, SerdeValueState.tables
    iframe D20 D12 D16 Hsb He Hw Hhex
  have s78 := SerdeStruct78Esc.f78_arr_copied (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) (sp - 64 + 48) (sp - 64) ptr idx 0 1 0 ob2 bs value rest j
    maxP mlen live F hob2 (by omega) hlen hptr (by omega) (by omega)
    ho hj hq he (by decide) hmodel hcopied hroom hvalid halloc
  rw [h48, hCS, ← hk] at s78
  ihave #S78 := s78 $$ [Hv F214 F169 F91 HC HP F228 Hi]
  · iframe Hv F214 F169 F91 HC HP F228 Hi
  clear s78
  mstep; mstep; mstep; mstep
  mcall S78 using [Hg S368 Hvt OB Hrd D24 Hstate]
  · iframe Hg S368 Hvt OB Hrd D24 Hstate
  icases HQ with ⟨%hrs, Hg, S368, Hvt, D24, %p, %cap, %l, %hp, W0, W4, W8, W12, ⟨Htables, Hvalue⟩, Hrd⟩
  subst hrs
  mcredits (590 * cfg.regularOpCost + W + R)
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
  mcredits (356 * cfg.regularOpCost + R)
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
  have s68 := SerdeScratchValueDrop.f68_value (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm
    (by omega) Cg maxP mlen live F (sp - 64) ptr 0 p cap l bs value.toUTF8.toList (j + 1)
    (by omega) hpos hbytes
  ihave #S68 := s68 $$ Hdrop
  clear s68
  mstep; mstep; mstep
  mcall S68 using [Hvalue]
  · iframe Hvalue
  icases HQ with ⟨%hrs, %scratch, %capS', D12, D16, D20, Hclean⟩
  subst hrs
  mcredits (5 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  iframe He Hw Hhex
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

end Proof
end WNear.Binary.SerdeFromTraitEsc
