import Bridge.Functions.SerdeStructEOF
import Bridge.Functions.SerdeStructObjRun
import Bridge.Functions.SerdeKeyReject
import Bridge.Functions.SerdeFixPosition
import Bridge.Functions.SerdeEndMapEOF
import Bridge.Functions.SerdeErrorDrop

/-! # An unfinished object rejects through the actual struct deserializer -/

namespace WNear.Binary.SerdeRej

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeStructArr (tbl roomS store1)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode)

theorem keyError_tag (e : UInt32) : SerdeKeyReject.errorPack e &&& 1 = 1 := by
  simp only [SerdeKeyReject.errorPack]
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

theorem keyError_ptr (e : UInt32) :
    (SerdeKeyReject.errorPack e >>> ((32 : UInt64) % 64)).toUInt32 = e := by
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp [SerdeKeyReject.errorPack, BitVec.getElem_and, BitVec.getElem_or,
    BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  interval_cases i <;> rfl

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- 228 rejects an object whose first key is missing at EOF. -/
theorem f228_obj_eof (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (hsp : 336 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hal : sp.toNat % 8 = 0) (hr : roomS mlen maxP)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (heof : i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) = bs.length) :
    endCode n maxP inst mi A ∗ A 193 ↪[wf] FuncInst.wasm types[11]! inst f193 ∗
      A 326 ↪[wf] FuncInst.wasm types[13]! inst f326 ∗
      A 327 ↪[wf] FuncInst.wasm types[13]! inst f327 ∗
      A 90 ↪[wf] FuncInst.wasm types[32]! inst f90 ∗
      A 92 ↪[wf] FuncInst.wasm types[0]! inst f92 ∗
      A 709 ↪[wf] FuncInst.wasm types[32]! inst f709 ∗ DropVec.dropCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de))
        (fun _ => (4000 + 96 * (wsLen (bs.drop i) + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))) * cfg.regularOpCost + costErr cfg F (bs.length + 1) + costErr cfg (max F 1) (bs.length + 1))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ tabs n de ∗
          rd n de ptr bs bs.length ∗ errRes n maxP out de live)) := by
  iintro ⟨#Hv, #F193, #F326, #F327, #F90, #F92, #F709, #HD⟩
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
  have ha90 := hm.funcs 90 (by decide)
  have ha92 := hm.funcs 92 (by decide)
  have ha193 := hm.funcs 193 (by decide)
  have ha326 := hm.funcs 326 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  have t13 : types[13]!.params.length = 2 := rfl
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 64 + 8).toNat = (sp - 64).toNat + 8 := by
    simp [UInt32.toNat_add]; omega
  generalize hw0 : wsLen (bs.drop i) = w0 at hb0 heof ⊢
  generalize hj0 : i + w0 = j0 at hb0 heof ⊢
  have hj0l := SerdeNextKey.getElem_lt hb0
  generalize hw1 : wsLen (bs.drop (j0 + 1)) = w1 at heof ⊢
  generalize hE : costErr cfg F (bs.length + 1) = E
  generalize hE2 : costErr cfg (max F 1) (bs.length + 1) = E2
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw0, hj0] at key
  simp only [Nat.mul_add, Nat.add_mul] at key ⊢
  generalize hW0 : 96 * w0 * cfg.regularOpCost = W0 at key ⊢
  generalize hW1 : 96 * w1 * cfg.regularOpCost = W1
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hd, Ht⟩
  subst hargs
  -- the frame and the stack below it
  icases stk_split n (sp.toNat - 336) 272 64 $$ Hs with ⟨S272, F64⟩
  rw [show sp.toNat - 336 + 272 = (sp - 64).toNat by omega,
    show sp.toNat - 336 = (sp - 64).toNat - 272 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨X0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 16 40 $$ F56 with ⟨R16, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16) 8 32 $$ F40 with ⟨X24, F32⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8) 4 28 $$ F32 with ⟨M32, F28⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8 + 4) 4 24 $$ F28 with ⟨M36, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8 + 4 + 4) 4 20 $$ F24 with ⟨M40, F20⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 8 + 4 + 4 + 4) 8 12 $$ F20 with ⟨M44, X52⟩
  rw [show (sp - 64).toNat + 8 + 16 + 8 + 4 + 4 + 4 + 8 = (sp - 64).toNat + 52 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 + 4 + 4 + 4 = (sp - 64).toNat + 44 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 + 4 + 4 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 + 4 = (sp - 64).toNat + 36 by omega,
    show (sp - 64).toNat + 8 + 16 + 8 = (sp - 64).toNat + 32 by omega,
    show (sp - 64).toNat + 8 + 16 = (sp - 64).toNat + 24 by omega]
  iunfold stk at M32 M36 M40 M44 R16
  icases M32 with ⟨%b32, %hb32, M32⟩
  icases M36 with ⟨%b36, %hb36, M36⟩
  icases M40 with ⟨%b40, %hb40, M40⟩
  icases M44 with ⟨%b44, %hb44, M44⟩
  icases R16 with ⟨%b16, %hb16, R16⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 36) 1 b36 (by omega) $$ M36 with ⟨M36, M37⟩
  simp only [f228]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (3800 * cfg.regularOpCost + W1 + E + E2 + R)
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb0]
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [Hd]
  ihave Hd := store1 n _ _ 127 SerdeStructObj.depth_down $$ Hd
  mstep; mstep
  mstep_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j0 hj0l
    (by omega) (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (3600 * cfg.regularOpCost + W1 + E + E2 + R)
  mstep; mstep; mstep [M36]
  ihave M36 := store1 n _ _ 1 (by decide) $$ M36
  mstep; mstep; mstep [M32]
  mstep; mstep; mstep [M40]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  let f0 := SerdeStructObj.fr228 inst mi out de x2 x3 x4 x5 (sp - 64) (optByte (some 123)) 127 0
  let I : List Value → Frame → IProp GF := fun X f =>
    iprop(⌜X = [] ∧ f = f0⌝ ∗ credits Cg (3500 * cfg.regularOpCost + W1 + E + E2 + R) ∗
      g ↦[wg] ⟨gt, .i32 (sp - 64)⟩ ∗ stk n ((sp - 64).toNat - 272) 272 ∗
      vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
      n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs (j0 + 1) ∗
      n ↦[wms][ de.toNat + 24 ] [127] ∗ tbl n de ∗
      stk n (sp - 64).toNat 8 ∗ n ↦[wms][ (sp - 64).toNat + 8 ] b16 ∗
      stk n ((sp - 64).toNat + 24) 8 ∗ n ↦[i32][ (sp - 64).toNat + 32 ] de ∗
      n ↦[wms][ (sp - 64).toNat + 36 ] [1] ∗
      n ↦[wms][ (sp - 64).toNat + 37 ] (b36.drop 1) ∗
      n ↦[i32][ (sp - 64).toNat + 40 ] 0 ∗ n ↦[wms][ (sp - 64).toNat + 44 ] b44 ∗
      stk n ((sp - 64).toNat + 52) 12)
  iapply mwpi_cons
  mcredits (cfg.regularOpCost + (3500 * cfg.regularOpCost + W1 + E + E2 + R))
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 3500 * cfg.regularOpCost + W1 + E + E2 + R) _ _ I rfl
  isplitr [Hc Hg S272 Hvt Hh Ho Hrd Hd Ht X0 R16 X24 M32 M36 M37 M40 M44 X52]
  · imodintro
    iintro %X %l HI
    simp only [I] at *
    icases HI with ⟨%⟨hX, hfr⟩, Hc, Hg, S272, Hvt, Hh, Ho, Hrd, Hd, Ht, X0, R16, X24, M32, M36, M37, M40, M44, X52⟩
    subst hX
    rw [hfr]
    simp only [f0, SerdeStructObj.fr228]
    have hA32 : (sp - 64 + 32).toNat = (sp - 64).toNat + 32 := by
      simp [UInt32.toNat_add]; omega
    have s193 := SerdeKeyReject.f193_eof (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
      (by omega) Cg gt (sp - 64) (sp - 64 + 32) de ptr idx 1 bs (j0 + 1) maxP mlen F live
      (by rw [hA32]; omega) hlen hptr hde (by omega) (by omega) hr.1 (by rw [hw1]; exact heof)
    rw [hA32, hw1, hE] at s193
    simp only [Nat.add_mul] at s193
    rw [hW1, show (sp - 64).toNat + 32 + 4 = (sp - 64).toNat + 36 by omega] at s193
    ihave #S193 := s193 $$ Hv
    clear s193
    icases stk_split n ((sp - 64).toNat - 272) 96 176 $$ S272 with ⟨S96, S176⟩
    rw [show (sp - 64).toNat - 272 + 96 = (sp - 64).toNat - 176 by omega]
    mstep; mstep; mstep; mstep
    mcall S193 using [M32 M36 Hg S176 Hvt Hh Hrd]
    · iframe M32 M36 Hg S176 Hvt Hh Hrd
    icases HQ with ⟨%e, %⟨hrs, he⟩, M32, M36, Hg, S176, Hvt, HE, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    rw [keyError_tag]
    mstep
    mstep_not_taken with decide
    mstep; mstep; mstep; mstep
    rw [keyError_ptr]
    mstep; mstep
    simp only [Post.mloop]
    mctrl_norm
    repeat mpay
    mcredits (2500 * cfg.regularOpCost + E2 + R)
    mstep; mstep; mstep [M40]; mstep
    mstep_taken with decide
    mstep; mstep
    iunfold SerdeErrorPositioned.heapPos at HE
    icases HE with ⟨HE, Ebox⟩
    iunfold SerdeErrBox.heapR at HE
    icases HE with ⟨%mlen1, %hmem1, Hh⟩
    have hroom1 : roomFor4 mlen1 maxP 20 := by
      have hc : (AllocNewCell.cellPages (AllocAlloc.wordsOf 20) 4).toNat = 1 := rfl
      simp only [hc, Nat.one_mul] at hmem1
      rcases hmem1 with rfl | rfl
      · exact hr.1
      · exact hr.2
    have s90 := SerdeEndMapEOF.f90_eof (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
      (by omega) Cg gt (sp - 64) de ptr idx bs bs.length maxP mlen1 (max F 1)
      ((e.toNat, 20) :: live) hlen hptr (by omega) (by omega) (by omega) hroom1
      (by simp [SerdeRead.wsLen])
    simp only [List.drop_length, SerdeRead.wsLen, Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at s90
    rw [hE2] at s90
    ihave #S90 := s90 $$ Hv
    clear s90
    icases stk_split n ((sp - 64).toNat - 176) 80 96 $$ S176 with ⟨S80, S96b⟩
    rw [show (sp - 64).toNat - 176 + 80 = (sp - 64).toNat - 96 by omega]
    mstep; mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep [Hd]
    ihave Hd := store1 n _ _ 128 SerdeStructObj.depth_up $$ Hd
    mstep
    mcall S90 using [Hg S96b Hvt Hh Hrd]
    · iframe Hg S96b Hvt Hh Hrd
    icases HQ with ⟨%e2, %b8, %⟨hrs, he2, hb8⟩, Hg, S96b, Hvt, HE2, Hrd⟩
    subst hrs
    mcredits (2000 * cfg.regularOpCost + R)
    icases U128From.memBytes_split n ((sp - 64).toNat + 8) 4 b16 (by omega) $$ R16 with ⟨R8, R16⟩
    icases U128From.memBytes_split n ((sp - 64).toNat + 8 + 4) 4 (b16.drop 4) (by simp; omega) $$ R16 with ⟨R12, R16⟩
    rw [show (sp - 64).toNat + 8 + 4 + 4 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega]
    iunfold stk at X24
    icases X24 with ⟨%b24, %hb24, X24⟩
    icases U128From.memBytes_split n ((sp - 64).toNat + 24) 4 b24 (by omega) $$ X24 with ⟨X24, X28⟩
    have hR16 : ((b16.drop 4).drop 4).length = 8 := by simp; omega
    have hR16ne : (b16.drop 4).drop 4 ≠ [] := List.ne_nil_of_length_pos (by rw [hR16]; omega)
    have hX24 : (b24.take 4).length = 4 := by simp; omega
    have hX24ne : b24.take 4 ≠ [] := List.ne_nil_of_length_pos (by rw [hX24]; omega)
    have hR12 : ((b16.drop 4).take 4).length = 4 := by simp; omega
    have hR12ne : (b16.drop 4).take 4 ≠ [] := List.ne_nil_of_length_pos (by rw [hR12]; omega)
    have hR8 : (b16.take 4).length = 4 := by simp; omega
    have hR8ne : b16.take 4 ≠ [] := List.ne_nil_of_length_pos (by rw [hR8]; omega)
    generalize hpack : SerdeKeyReject.errorPack e = packed
    mstep; mstep; mstep; mstep; mstep; mstep [R16] with (simp [UInt32.toNat_add]; omega)
    mstep; mstep; mstep [X24]
    mstep; mstep; mstep [R12]
    mstep; mstep; mstep [R8]
    mstep; mstep
    mstep_taken with decide
    mstep; mstep; mstep; mstep
    have he2b : Numeric.bool (e2 == 0) = 0 := by simp [Numeric.bool, he2]
    mstep_not_taken with exact he2b
    mstep; mstep; mstep
    iunfold SerdeErrorCode.heapPos at HE2
    icases HE2 with ⟨HE2, Ebox2⟩
    iunfold SerdeErrBox.heapR at HE2
    icases HE2 with ⟨%mlen2, %hmem2, Hh⟩
    iunfold SerdeErrorCode.positionedBox at Ebox2
    icases Ebox2 with ⟨%line2, %col2, %⟨hp2, hc2, hline2⟩, Code2, Line2, Col2⟩
    icases (memBytes_append n e2.toNat (bytes32 3) b8).1 $$ Code2 with ⟨Tag2, Tail2⟩
    simp only [bytes32_length]
    ihave Tail12 := U128From.memBytes_join n (e2.toNat + 4) 8 b8 (bytes32 line2) hb8 $$ [Tail2 Line2]
    · rw [show e2.toNat + 4 + 8 = e2.toNat + 12 by omega]
      iframe Tail2 Line2
    ihave Tail16 := U128From.memBytes_join n (e2.toNat + 4) 12 (b8 ++ bytes32 line2) (bytes32 col2)
      (by simp [hb8]) $$ [Tail12 Col2]
    · rw [show e2.toNat + 4 + 12 = e2.toNat + 16 by omega]
      iframe Tail12 Col2
    have hA24 : (sp - 64 + 24).toNat = (sp - 64).toNat + 24 := by simp [UInt32.toNat_add]; omega
    have s92 := SerdeErrorDrop.f92_syntax (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm
      (by omega) Cg maxP mlen2 ((e2.toNat, 20) :: (e.toNat, 20) :: live) (max (max F 1) 1)
      (sp - 64 + 24) e2 3 ((b8 ++ bytes32 line2) ++ bytes32 col2) (by rw [hA24]; omega) hp2
      (by decide) (by simp [hb8]) (by simp)
    rw [hA24] at s92
    ihave #S92 := s92 $$ [HD F709]
    · iframe HD F709
    clear s92
    mcall S92 using [X24 Tag2 Tail16 Hh]
    ·
      iframe X24 Tag2 Tail16 Hh
    icases HQ with ⟨%hrs, X24, Hh⟩
    subst hrs
    mstep
    mcredits (1200 * cfg.regularOpCost + R)
    mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    icases stk_split n ((sp - 64).toNat - 96) 80 16 $$ S96b with ⟨S80b, S16⟩
    rw [show (sp - 64).toNat - 96 + 80 = (sp - 64).toNat - 16 by omega]
    ihave #S326 := SerdeErrorPositioned.f326_positioned (GF := GF) cfg lim (d + 1) types[13]! rfl
      inst mi A n g ta hm (by omega) Cg gt (sp - 64) de e (by omega) $$ [Hi F327]
    · iframe Hi F327
    mcall S326 using [Hg S16 Ebox] with
      (first | assumption | rfl | (simp only [List.length_cons, List.length_nil]; omega) | (mstep_norm_full; omega))
    · iframe Hg S16 Ebox
    icases HQ with ⟨%hrs, Hg, S16, Ebox⟩
    subst hrs
    icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
    icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
    have hO0 : (ob.take 4).length = 4 := by simp; omega
    have hO0ne : ob.take 4 ≠ [] := List.ne_nil_of_length_pos (by rw [hO0]; omega)
    have hO4 : ((ob.drop 4).take 4).length = 4 := by simp; omega
    have hO4ne : (ob.drop 4).take 4 ≠ [] := List.ne_nil_of_length_pos (by rw [hO4]; omega)
    mstep [O4]
    mstep; mstep; mstep
    mstep; mstep; mstep [O0]
    mcredits (10 * cfg.regularOpCost + R)
    mstep; mstep; mstep
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
    rw [show sp - 64 + 64 = sp by simp]
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
    iframe Hg Hvt Hd Hrd
    isplitr
    · ipureintro; simp [htype]
    isplitl [S96 S80 S80b S16 X0 R8 R12 R16 X24 X28 M32 M36 M37 M40 M44 X52]
    · ihave R8 := stk_word n _ _ $$ R8
      ihave R12 := stk_word n _ _ $$ R12
      ihave R16 := stk_intro n _ _ $$ R16
      rw [show (storeBytes (Value.i64 packed) 8).length = 8 by simp [storeBytes]]
      ihave X24 := stk_word n _ _ $$ X24
      ihave X28 := stk_intro n _ _ $$ X28
      rw [show (b24.drop 4).length = 4 by simp; omega]
      ihave M32 := stk_word n _ _ $$ M32
      ihave M36 := stk_intro n _ _ $$ M36
      ihave M37 := stk_intro n _ _ $$ M37
      ihave M40 := stk_word n _ _ $$ M40
      ihave M44 := stk_intro n _ _ $$ M44
      rw [show (b36.drop 1).length = 3 by simp; omega, hb44]
      simp only [List.length_cons, List.length_nil]
      rw [show (sp - 64).toNat + 24 + 4 = (sp - 64).toNat + 28 by omega]
      ihave F64 := SerdeStructObj.frame64o n (sp - 64).toNat $$ [X0 R8 R12 R16 X24 X28 M32 M36 M37 M40 M44 X52]
      · iframe X0 R8 R12 R16 X24 X28 M32 M36 M37 M40 M44 X52
      ihave S96b := stk_join n ((sp - 64).toNat - 96) 80 16 $$ [S80b S16]
      · rw [show (sp - 64).toNat - 96 + 80 = (sp - 64).toNat - 16 by omega]
        iframe S80b S16
      ihave S176 := stk_join n ((sp - 64).toNat - 176) 80 96 $$ [S80 S96b]
      · rw [show (sp - 64).toNat - 176 + 80 = (sp - 64).toNat - 96 by omega]
        iframe S80 S96b
      ihave S272 := stk_join n ((sp - 64).toNat - 272) 96 176 $$ [S96 S176]
      · rw [show (sp - 64).toNat - 272 + 96 = (sp - 64).toNat - 176 by omega]
        iframe S96 S176
      iapply stk_join n ((sp - 64).toNat - 272) 272 64
      rw [show (sp - 64).toNat - 272 + 272 = (sp - 64).toNat by omega]
      iframe S272 F64
    ihave Ht := tbl_tabs n de $$ Ht
    icases Ht with ⟨Ht, D12, D16⟩
    iframe Ht
    iunfold errRes
    iexists e, (1 : UInt32), (0 : UInt32), ((ob.drop 4).drop 4), ((e.toNat, 20) :: live), mlen2,
      (max (max F 1) 1 + 1)
    simp only [List.erase_cons_head, UInt32.reduceToNat]
    rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
    iframe O0 O4 O8 Hh D12 D16
    isplitr
    · ipureintro
      refine ⟨by simp; omega, Or.inl ⟨rfl, .cons _ (.refl live)⟩⟩
    iunfold scrBlk
    simp only [ite_true]
    iempintro
  · isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    simp only [I, f0, SerdeStructObj.fr228]
    iframe Hc Hg S272 Hvt Hh Ho Hrd Hd Ht X0 R16 X24 M32 M36 M37 M40 M44 X52
    ipureintro
    exact ⟨trivial, rfl⟩

/-- The missing first key at EOF discharges the rejecting 228 contract. -/
theorem rej228_obj_eof (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType)
    (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 25 ≤ 2 ^ 32) (hb0 : bs[wsLen bs]? = some 0x7B)
    (heof : wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) = bs.length)
    (Cd : IProp GF) [Persistent Cd] (hc : Cd ⊢ endCode n maxP inst mi A ∗ A 193 ↪[wf] FuncInst.wasm types[11]! inst f193 ∗
      A 326 ↪[wf] FuncInst.wasm types[13]! inst f326 ∗
      A 327 ↪[wf] FuncInst.wasm types[13]! inst f327 ∗
      A 90 ↪[wf] FuncInst.wasm types[32]! inst f90 ∗
      A 92 ↪[wf] FuncInst.wasm types[0]! inst f92 ∗
      A 709 ↪[wf] FuncInst.wasm types[32]! inst f709 ∗ DropVec.dropCode inst mi A) :
    Rej228 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP
      (fun F => (4000 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)))) * cfg.regularOpCost + costErr cfg F (bs.length + 1) + costErr cfg (max F 1) (bs.length + 1)) Cd := by
  intro d sp out ob mlen F live hd hob hout hsp hal hr
  have hs := f228_obj_eof (GF := GF) cfg lim d types[36]! rfl inst mi A n g ta hm hd Cg gt sp out de ptr idx
    out out out out ob bs 0 maxP mlen F live hob hout hlen hptr hde hsp (Nat.zero_le _) hal hr (by simpa using hb0)
    (by simpa using heof)
  simp only [List.drop_zero, Nat.zero_add] at hs
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
