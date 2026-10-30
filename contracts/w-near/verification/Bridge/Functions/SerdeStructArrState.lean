import Bridge.Functions.SerdeStructArr
import Bridge.Functions.SerdeColonSuccess

/-!
# Array struct deserialization with a changing-state value reader

The successful element reader owns its heap and scratch in P and returns Q. The
closing bracket path frames that state through without reopening a heap invariant
at the old memory length. The complete frame includes the general string reader.
-/

namespace WNear.Binary.SerdeStructArrState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeEnds (endCode some_bit)
open WNear.Binary.SerdeErrBox (errCode)
open WNear.Binary.SerdeStructArr (store1 frame64 depth_back)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- The array struct path preserves any changing state returned by its successful 169 callee. -/
theorem f228_arr_state (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP : Nat) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hi : i ≤ bs.length)
    (P : IProp GF) (K169 : Nat) (Q : UInt32 → UInt32 → UInt32 → IProp GF) (Cd : IProp GF)
    [Persistent Cd] (r : List UInt8)
    (hok : bs[i + wsLen (bs.drop i)]? = some 0x5B ∧
      (∃ b, bs[i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1))]? = some b ∧ b ≠ 0x5D) ∧
      bs[bs.length - r.length + wsLen (bs.drop (bs.length - r.length))]? = some 0x5D)
    (h169 : ∀ ob1 : List UInt8, ob1.length = 16 →
      Cd ⊢ SerdeSeqElem.Spec169 cfg lim (d + 2) inst mi n g Cg gt (sp - 64) de ptr ob1 bs
        (i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))
        iprop(stk n ((sp - 64).toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗ P)
        K169 (fun p c l => iprop(stk n ((sp - 64).toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          rd n de ptr bs (bs.length - r.length) ∗ Q p c l))) :
    endCode n maxP inst mi A ∗ A 214 ↪[wf] FuncInst.wasm types[14]! inst f214 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ A 91 ↪[wf] FuncInst.wasm types[32]! inst f91 ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ P))
        (fun _ => (1300 + 96 * (wsLen (bs.drop i) +
          wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) + wsLen (bs.drop (bs.length - r.length)))) *
          cfg.regularOpCost + K169)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          ∃ (p c l : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] l ∗ Q p c l ∗
            rd n de ptr bs (bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) + 1))) := by
  iintro ⟨#Hv, #F214, #F169, #F91, #HCd⟩
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha214 := hm.funcs 214 (by decide)
  have ha91 := hm.funcs 91 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  obtain ⟨hb0, ⟨b, hb2, hb93⟩, hb4⟩ := hok
  generalize hw0 : wsLen (bs.drop i) = w0 at hb0 hb2 ⊢
  generalize hj0 : i + w0 = j0 at hb0 hb2 ⊢
  have hj0l := SerdeNextKey.getElem_lt hb0
  generalize hw2 : wsLen (bs.drop (j0 + 1)) = w2 at hb2 ⊢
  generalize hj2 : j0 + 1 + w2 = j2 at hb2 ⊢
  have hj2l := SerdeNextKey.getElem_lt hb2
  generalize hj3 : bs.length - r.length = j3 at hb4 ⊢
  generalize hw4 : wsLen (bs.drop j3) = w4 at hb4 ⊢
  have hj4l := SerdeNextKey.getElem_lt hb4
  generalize hK : K169 = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Ho, Hrd, Hd, Hstate⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  -- the frame and the stack below it
  icases stk_split n (sp.toNat - 368) 288 80 $$ Hs with ⟨S288, S80⟩
  icases stk_split n (sp.toNat - 368 + 288) 16 64 $$ S80 with ⟨S16, F64⟩
  rw [show sp.toNat - 368 + 288 + 16 = (sp - 64).toNat by omega,
    show sp.toNat - 368 + 288 = (sp - 64).toNat - 16 by omega,
    show sp.toNat - 368 = (sp - 64).toNat - 304 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨X0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 16 40 $$ F56 with ⟨R16, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16) 16 24 $$ F40 with ⟨X24, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 16) 8 16 $$ F24 with ⟨A8, X48⟩
  rw [show (sp - 64).toNat + 8 + 16 + 16 + 8 = (sp - 64).toNat + 48 by omega,
    show (sp - 64).toNat + 8 + 16 + 16 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 16 = (sp - 64).toNat + 24 by omega]
  icases stk_split n ((sp - 64).toNat + 24) 4 12 $$ X24 with ⟨X24, X28⟩
  iunfold stk at A8 R16 S16 X24
  icases A8 with ⟨%ba, %hba, A8⟩
  icases R16 with ⟨%ob2, %hob2, R16⟩
  icases S16 with ⟨%ob1, %hob1, S16⟩
  icases X24 with ⟨%bx, %hbx, X24⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 40) 4 ba (by omega) $$ A8 with ⟨A40, A44⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 40 + 4) 1 (ba.drop 4) (by simp; omega) $$ A44 with ⟨A44, A45⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
  rw [show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  -- the callees
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw0, hj0] at key
  generalize hW0 : (100 + 96 * w0) * cfg.regularOpCost = W0 at key
  have h80 : (sp - 64 - 16).toNat = (sp - 64).toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  have hO8 : (sp - 64 + 8).toNat = (sp - 64).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have hA40 : (sp - 64 + 40).toNat = (sp - 64).toNat + 40 := by simp [UInt32.toNat_add]; omega
  have s214 := SerdeSeqElem.f214_first (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 64) (sp - 64 + 8) (sp - 64 + 40) de ptr ob1 ob2 bs (j0 + 1) b maxP hob1 hob2 (by omega) hlen hptr
    (by omega) (by omega) (by omega) (by omega) (by rw [hw2, hj2]; exact hb2) hb93
    iprop(stk n ((sp - 64).toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗ P) K
    (fun p c l => iprop(stk n ((sp - 64).toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
      rd n de ptr bs (bs.length - r.length) ∗ Q p c l))
  rw [hO8, hA40, hw2, hj2, hj3, h80,
    show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega] at s214
  have sp169 := h169 ob1 hob1
  rw [hw0, hj0, hw2, hj2, hK, hj3] at sp169
  ihave #Sp169 := sp169 $$ HCd
  clear sp169
  generalize hT214 : (300 + 96 * w2) * cfg.regularOpCost + K = T214 at s214
  ihave #S214 := s214 $$ [Hv F169 Sp169]
  · iframe Hv F169 Sp169
  clear s214
  rw [show (1300 + 96 * (w0 + w2 + w4)) * cfg.regularOpCost + K + R =
    100 * cfg.regularOpCost + (W0 + (150 * cfg.regularOpCost + (T214 + (60 * cfg.regularOpCost +
      ((400 + 96 * w4) * cfg.regularOpCost + (190 * cfg.regularOpCost + R)))))) by
      rw [← hW0, ← hT214]; simp only [Nat.add_mul, Nat.mul_add]; omega]
  generalize hT91 : (400 + 96 * w4) * cfg.regularOpCost = T91
  simp only [f228]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (230 * cfg.regularOpCost + (T214 + (60 * cfg.regularOpCost + (T91 + (190 * cfg.regularOpCost + R)))))
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
  mstep_taken with decide
  mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [Hd]
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j0 hj0l
    (by omega) (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (160 * cfg.regularOpCost + (T214 + (60 * cfg.regularOpCost + (T91 + (190 * cfg.regularOpCost + R)))))
  mstep; mstep; mstep [A40]
  mstep; mstep; mstep [A44]
  ihave A44 := store1 n _ 1 1 (by decide) $$ A44
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S214 using [A40 A44 Hg S16 R16 Hrd S288 Hvt Hstate]
  · iframe A40 A44 Hg S16 R16 Hrd S288 Hvt Hstate
  icases HQ with ⟨%hrs, A40, A44, Hg, S16, %p, %c, %l, %hp, W8, W12, W16, W20, S288, Hvt, Hrd, Hstate⟩
  subst hrs
  mcredits (100 * cfg.regularOpCost + (T91 + (190 * cfg.regularOpCost + R)))
  mstep; mstep; mstep; mstep [W8]; mstep; mstep
  mstep_taken with decide
  mstep; mstep [W12]; mstep
  mstep_taken with (simp [Numeric.bool, hp])
  ihave W16 := KeyGet.join64 n ((sp - 64).toNat + 8 + 8) c (l) $$ [W16 W20]
  · rw [show (sp - 64).toNat + 8 + 8 + 4 = (sp - 64).toNat + 8 + 12 by omega]; iframe W16 W20
  mstep; mstep; mstep
  mstep [W16] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.ofNat_decode_pair]
  mstep; mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  have s91 := SerdeColonSuccess.f91_close (GF := GF) cfg lim (d + 1) types[32]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 64) de ptr bs j3 (by omega) (by omega) (by omega) (by omega)
    (by rw [hw4]; exact hb4)
  rw [hw4, hT91] at s91
  ihave #S91 := s91 $$ [F332 F333 F339 Hi]
  · iframe F332 F333 F339 Hi
  clear s91
  ihave S16 := stk_addr (show (sp - 64).toNat - 16 = (sp - 64).toNat - 304 + 288 by omega) $$ S16
  ihave S304 := stk_join n ((sp - 64).toNat - 304) 288 16 $$ [S288 S16]
  · iframe S288 S16
  icases stk_split n ((sp - 64).toNat - 304) 192 112 $$ S304 with ⟨S192, S112⟩
  rw [show (sp - 64).toNat - 304 + 192 = (sp - 64).toNat - 112 by omega]
  mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [Hd]
  mstep
  mcall S91 using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  mcredits (150 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep; mstep
  mstep [W16] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep [X24] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [W12] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [W8] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep_not_taken with decide
  mstep
  mstep_not_taken with decide
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep [O4]
  mstep; mstep; mstep; mstep; mstep [O8] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  isplitl [S192 S112 X0 W8 W12 W16 X24 X28 A40 A44 A45 X48]
  · ihave S112 := stk_addr (show (sp - 64).toNat - 112 = (sp - 64).toNat - 304 + 192 by omega) $$ S112
    ihave S304 := stk_join n ((sp - 64).toNat - 304) 192 112 $$ [S192 S112]
    · iframe S192 S112
    ihave W8 := stk_word $$ W8
    ihave W12 := stk_word $$ W12
    ihave W16 := stk_intro $$ W16
    ihave X24 := stk_word $$ X24
    ihave A40 := stk_word $$ A40
    ihave A44 := stk_intro $$ A44
    ihave A45 := stk_intro $$ A45
    rw [show (bytes32 c ++ bytes32 (l)).length = 8 by simp,
      show (List.drop 1 (List.drop 4 ba)).length = 3 by simp; omega,
      show ([0] : List UInt8).length = 1 by rfl,
      show (sp - 64).toNat + 8 + 8 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega,
      show (sp - 64).toNat + 24 + 4 = (sp - 64).toNat + 28 by omega,
      show (sp - 64).toNat + 44 + 1 = (sp - 64).toNat + 45 by omega]
    ihave F64 := frame64 n (sp - 64).toNat $$ [X0 W8 W12 W16 X24 X28 A40 A44 A45 X48]
    · iframe X0 W8 W12 W16 X24 X28 A40 A44 A45 X48
    ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 304 + 304 by omega) $$ F64
    iapply stk_join n ((sp - 64).toNat - 304) 304 64
    iframe S304 F64
  isplitl [Hd]
  · iapply (store1 n _ _ 128 depth_back)
    iexact Hd
  iexists p, c, l
  isplitr
  · ipureintro; exact hp
  ihave O8 := KeyGet.split64 n (out.toNat + 8) c l $$ O8
  icases O8 with ⟨O8, O12⟩
  rw [show out.toNat + 8 + 4 = out.toNat + 12 by omega]
  iframe O0 O4 O8 O12 Hrd Hstate

end Proof
end WNear.Binary.SerdeStructArrState
