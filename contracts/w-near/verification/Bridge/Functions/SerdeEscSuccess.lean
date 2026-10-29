import Bridge.Functions.SerdeEscRead

/-!
# Constant-cost readers on a successful escape path

Successful `next_or_eof` and hex decoding never construct an error. Their
contracts reserve only the instructions that execute, so repeated successful
escapes do not pay for repeated whole-input source-position scans.
-/

namespace WNear.Binary.SerdeEscSuccess

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd optByte)
open WNear.Binary.SerdeEsc
open WNear.Binary.SerdeErrBox (roomFor4 errCode)
open NearInterface.Json (hexValue hex4)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A present byte is returned without touching the allocator or stack memory. -/
theorem f655_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g a637 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (ha637 : mi.funcAddrs[637]? = some a637) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i < bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ a637 ↪[wf] FuncInst.wasm types[11]! inst f637 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f655 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs i))
        (fun _ => 100 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (okPack de bs[i])]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs (i + 1))) := by
  iintro ⟨#Hi, #F637⟩
  have t11 : types[11]!.params.length = 1 := rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, Hg, Hrd⟩
  subst ha
  simp only [f655]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeRead.f637_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n hn Cg de ptr bs i hi.le
    hlen hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hi
  rw [hb]
  have hok : Numeric.bool (optByte (some bs[i]) &&& 1 == 0) = 1 := by
    simp only [SerdeRead.optByte_ok]; rfl
  have hz : Numeric.bool (Numeric.irelop64 IRelOp.eq (optByte (some bs[i]) &&& 256) 0) = 0 := by
    generalize bs[i] = b; revert b; exact SerdeRead.uint8_forall (by decide +kernel)
  repeat mstep
  mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg
  isplitr
  · ipureintro
    simpa [htype] using congrArg (fun v : UInt64 => [Value.i64 v]) (okPack_eq de bs[i])
  rw [show min (i + 1) bs.length = i + 1 by omega]
  iexact Hrd

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`decode_hex_escape(rd)`** (653) on four valid hex digits, without an error reserve. -/
theorem f653_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat) (maxP mlen : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 8 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat)
    (hvalid : (hex4 (bs.drop i)).isSome = true) :
    eofCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f653 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i ∗ n ↦[wms][ 1062712 ] hexTable))
        (fun _ => 300 * cfg.regularOpCost)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res653 n maxP mlen live F de ptr bs i rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold eofCode at Hk'
  icases Hk' with ⟨#HE, -, -, #H654, -, -⟩
  ihave #HE' := HE
  iunfold errCode at HE'
  icases HE' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha654 := hm.funcs 654 (by decide)
  have t30 : types[30]!.params.length = 2 := by rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hiu : (UInt32.ofNat i).toNat = i := by simp; omega
  have hlu : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  have hi4 : (UInt32.ofNat i + 4).toNat = i + 4 := by rw [UInt32.toNat_add, hiu]; simp; omega
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat i + 4) (UInt32.ofNat i)) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hi4, hiu]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hrd, Ht⟩
  subst hargs
  iunfold rd, ArgsLeaves.sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  icases stk_split n (sp.toNat - 96) 80 16 $$ Hs with ⟨Lo, Fr⟩
  icases stk_split n (sp.toNat - 96 + 80) 4 12 $$ Fr with ⟨C0, C4⟩
  icases stk_split n (sp.toNat - 96 + 80 + 4) 8 4 $$ C4 with ⟨C4, U⟩
  iunfold stk at C0 C4
  icases C0 with ⟨%c0, %hc0, C0⟩
  icases C4 with ⟨%c4, %hc4, C4⟩
  ihave C0 := memBytes_addr (show sp.toNat - 96 + 80 = (sp - 16).toNat by omega) $$ C0
  ihave C4 := memBytes_addr (show sp.toNat - 96 + 80 + 4 = (sp - 16).toNat + 4 by omega) $$ C4
  ihave Lo := stk_addr (show sp.toNat - 96 = (sp - 16).toNat - 80 by omega) $$ Lo
  simp only [f653]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [D8]
  repeat mstep
  mstep [D4]
  repeat mstep
  by_cases h4 : i + 4 ≤ bs.length
  · have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat i + 4) (UInt32.ofNat bs.length)) = 0 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hi4, hlu]; omega
    repeat mstep
    mstep [D0]
    repeat mstep
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 240 * cfg.regularOpCost + (0 + R))
      (I := inv653 n inst mi Cg cfg.regularOpCost (40 * cfg.regularOpCost) (0 + R) de (sp - 16) bs i ptr
        iprop(g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n ((sp - 16).toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ 1062712 ] hexTable ∗ n ↦[i32][ de.toNat ] ptr ∗
          n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ (sp - 16).toNat ] c0 ∗ n ↦[wms][ (sp - 16).toNat + 4 ] c4 ∗
          stk n (sp.toNat - 96 + 80 + 4 + 8) 4)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv653 at HI
      icases HI with ⟨%k, %acc, %l9, %l10, %⟨hX, hfr, hk4, hacc⟩, Hc, D8, Hg, Lo, Hvt, Hinv, Ht, D0, D4, Hb, C0, C4, U⟩
      subst hX
      rw [hfr]
      clear hfr
      have hku : (UInt32.ofNat k).toNat = k := by simp; omega
      by_cases hk : k = 4
      · subst hk
        have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat 4) 4) = 0 := by decide
        have hx : hex4 (bs.drop i) = some (acc, bs.drop (i + 4)) := by
          rw [hex4_eq]; simp only [List.length_drop, show 4 ≤ bs.length - i by omega, ite_true, hacc]
          simp [List.drop_drop, Nat.add_comm]
        repeat mstep
        simp only [Post.mloop]
        mctrl_norm
        repeat mpay
        repeat mstep
        mstep [Hg]
        rw [show sp - 16 + 16 = sp by simp]
        repeat mstep
        mcredits R
        have hacc4 := hexAcc_lt _ _ hacc
        simp only [List.length_take, List.length_drop, show min 4 (bs.length - i) = 4 by omega] at hacc4
        iframe Hc Hg Hvt Ht
        simp only [res653, hx, htype, Nat.sub_self, List.drop_zero, hexPack_eq acc (by omega)]
        isplitr [Hinv D0 D4 D8 Hb]
        · ihave Lo := stk_addr (show (sp - 16).toNat - 80 = sp.toNat - 96 by omega) $$ Lo
          ihave C := U128From.memBytes_join n (sp - 16).toNat 4 c0 c4 hc0 $$ [C0 C4]
          · iframe C0 C4
          ihave C := stk_intro n _ _ $$ C
          rw [show (c0 ++ c4).length = 12 by simp; omega]
          ihave C := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ C
          ihave C := stk_join n (sp.toNat - 96 + 80) 12 4 $$ [C U]
          · iframe C
            iapply stk_addr (show sp.toNat - 96 + 80 + 4 + 8 = sp.toNat - 96 + 80 + 12 by omega) $$ U
          iapply stk_join n (sp.toNat - 96) 80 16
          iframe Lo C
        iframe Hinv
        iunfold rd, ArgsLeaves.sliceRead
        iframe D0 D4 D8 Hb
      · have hk3 : k < 4 := by omega
        have hikl : i + k < bs.length := by omega
        have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat k) 4) = 1 := by
          have : UInt32.ofNat k ≠ 4 := fun e => by have := congrArg UInt32.toNat e; rw [hku] at this; simp at this; omega
          simp [Numeric.irelop32, Numeric.bool, this]
        have hik : (UInt32.ofNat i + UInt32.ofNat k).toNat = i + k := by rw [UInt32.toNat_add, hiu, hku]; simp; omega
        have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i + UInt32.ofNat k) (UInt32.ofNat bs.length)) = 0 := by
          simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le, hik, hlu]; omega
        ihave Hb := MemCpy.memBytes_pick n ptr.toNat (i + k) bs hikl $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        obtain ⟨x, hxk⟩ : ∃ x, bs[i + k] = x := ⟨_, rfl⟩
        rw [hxk]
        have es : List.take (i + k) bs ++ x :: List.drop (i + k + 1) bs = bs := by rw [← hxk]; simp
        have hx256 := x.toNat_lt
        have htk : (bs.drop i).take (k + 1) = (bs.drop i).take k ++ [x] := by
          rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem hikl, hxk]; rfl
        rw [show (4 - k) * 50 * cfg.regularOpCost + 40 * cfg.regularOpCost + (0 + R) =
          50 * cfg.regularOpCost + ((4 - (k + 1)) * 50 * cfg.regularOpCost + 40 * cfg.regularOpCost + (0 + R)) by
            rw [show 4 - k = (4 - (k + 1)) + 1 by omega]; simp only [Nat.add_mul]; omega]
        generalize hZ : (4 - (k + 1)) * 50 * cfg.regularOpCost = Z
        repeat mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.load8]
        ihave Hb := MemCpy.memBytes_unpick n ptr.toNat (i + k) (bs.take (i + k)) x (bs.drop (i + k + 1)) (by simp; omega) $$ [B1 Bk B2]
        · iframe B1 Bk B2
        rw [es]
        repeat mstep
        mstep [D8]
        repeat mstep
        ihave Ht := MemCpy.memBytes_pick n 1062712 x.toNat hexTable (by rw [hexTable_length]; exact x.toNat_lt) $$ Ht
        icases Ht with ⟨T1, Tk, T2⟩
        mstep [Tk] with (simp [UInt32.toNat_add]; omega)
        rw [SerdeKey.load8, hex_at]
        ihave Ht := MemCpy.memBytes_unpick n 1062712 x.toNat (hexTable.take x.toNat) _ (hexTable.drop (x.toNat + 1)) (by simp [hexTable_length]; omega) $$ [T1 Tk T2]
        · iframe T1 Tk T2
        rw [show List.take x.toNat hexTable ++ hexTable[x.toNat]'(by rw [hexTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) hexTable = hexTable by simp]
        have hd1 : UInt32.ofNat i + UInt32.ofNat k + 1 = UInt32.ofNat (i + (k + 1)) := by
          apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hik]; simp; omega
        rw [hd1]
        cases hv : hexValue x with
        | none =>
          have hnone : hexAcc ((bs.drop i).take (k + 1)) = none := by rw [htk, hexAcc_snoc, hacc]; simp [hv]
          have hx : hex4 (bs.drop i) = none := by
            rw [hex4_eq]
            split
            · have e : (bs.drop i).take 4 = (bs.drop i).take (k + 1) ++ ((bs.drop i).take 4).drop (k + 1) := by
                conv => lhs; rw [← List.take_append_drop (k + 1) ((bs.drop i).take 4)]
                rw [List.take_take, show min (k + 1) 4 = k + 1 by omega]
              rw [e, hexAcc_append_none _ _ hnone]; rfl
            · rfl
          exfalso
          simpa [hx] using hvalid
        | some v =>
          have hv16 := hexValue_lt x v hv
          have hacc' : hexAcc ((bs.drop i).take (k + 1)) = some (acc * 16 + v) := by
            rw [htk, hexAcc_snoc, hacc]; simp [hv]
          have haccl := hexAcc_lt _ _ hacc
          simp only [List.length_take, List.length_drop, show min k (bs.length - i) = k by omega] at haccl
          have hk16 : 16 ^ k ≤ 4096 := by interval_cases k <;> decide
          have h255 : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat v) 255) = 0 := by
            have : UInt32.ofNat v ≠ 255 := fun e => by
              have := congrArg UInt32.toNat e; simp at this; omega
            simp [Numeric.irelop32, Numeric.bool, this]
          have hsh := shl4_mask acc v (by omega) hv16
          have hmask : Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat (acc * 16 + v) &&& 65535)
              (UInt32.ofNat (acc * 16 + v))) = 0 := by
            have : UInt32.ofNat (acc * 16 + v) &&& 65535 = UInt32.ofNat (acc * 16 + v) := by
              have hw : (UInt32.ofNat (acc * 16 + v)).toNat = acc * 16 + v := by
                rw [UInt32.toNat_ofNat']; omega
              generalize UInt32.ofNat (acc * 16 + v) = w at hw ⊢
              apply UInt32.toNat_inj.mp
              rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hw]
              omega
            rw [this]; simp [Numeric.irelop32, Numeric.bool]
          dsimp only
          mstep; mstep; mstep
          mstep
          mstep; mstep; mstep; mstep; mstep; mstep; mstep
          rw [hsh]
          repeat mstep
          rw [SerdeRead.ofNat_succ k (by omega)]
          simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iunfold inv653
          iexists k + 1, acc * 16 + v, UInt32.ofNat v, x.toUInt32
          iframe Hg Lo Hvt Hinv Ht D0 D4 Hb C0 C4 U D8
          isplitr
          · ipureintro; exact ⟨rfl, rfl, by omega, hacc'⟩
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
    · isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      inext
      iintro Hc
      iunfold inv653
      iexists 0, 0, 0, 0
      iframe Hg Lo Hvt Hinv Ht D0 D4 Hb C0 C4 U
      isplitr
      · ipureintro; exact ⟨rfl, rfl, by omega, by simp [hexAcc]⟩
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      rw [Nat.add_zero]
      iexact D8
  · have hx : hex4 (bs.drop i) = none := by rw [hex4_eq]; simp; omega
    exfalso
    simpa [hx] using hvalid

end Proof
end WNear.Binary.SerdeEscSuccess
