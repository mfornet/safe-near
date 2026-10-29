import Bridge.Functions.SerdeEscErr

/-!
# `next_or_eof` (655) and `decode_hex_escape` (653) (M6)

`parse_escape` (649) reads the escape's bytes with two functions:

```wat
;; 655 next_or_eof(rd) → i64       SliceRead::next (637); Some(b) ⇒ Ok(b) = (rd << 32) | (b << 8);
;;                                  None ⇒ 656(rd, EofWhileParsingString), packed `Err(box)`
;; 653 decode_hex_escape(rd) → i64 index + 4 > len ⇒ index := len, 654(EofWhileParsingString);
;;                                  else four hex digits through the table at 1062712 (255: not a
;;                                  digit ⇒ 654(InvalidEscape) at the index past it);
;;                                  Ok(n) = n << 16
```

* `f655_spec`: `res655`, `Ok` with the byte at the index (the reader moves past it), or `Err(box)` at
  the end of the input.
* `hexTable`, `hexData_segment`: the table.
* `f653_spec`: `res653`, `Ok(n)` on four hex digits (`hex4`, the model's), else `Err(box)`.
-/

namespace WNear.Binary.SerdeEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd optByte)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4 errPack f654_spec f656_eq)

/-- The packed `Ok(b)` of 655: the reader's address above, the byte at bits 8..15. -/
def okPack (de : UInt32) (b : UInt8) : UInt64 := de.toUInt64 <<< 32 ||| b.toUInt64 <<< 8

theorem okPack_eq (de : UInt32) (b : UInt8) :
    ((0 : UInt64) ||| 0 ||| de.toUInt64 <<< ((32 : UInt64) % 64) |||
      optByte (some b) >>> ((16 : UInt64) % 64) <<< ((8 : UInt64) % 64) &&& (65280 : UInt64)) =
      okPack de b := by
  simp only [optByte, okPack]
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

theorem toUInt32_toUInt64 (y : UInt64) : y.toUInt32.toUInt64 = y &&& (4294967295 : UInt64) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, UInt64.toNat_and]
  rw [show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem errPack_repack (p : UInt32) :
    (errPack p &&& (255 : UInt64) ||| errPack p &&& (4294901760 : UInt64) |||
      (errPack p >>> ((32 : UInt64) % 64)).toUInt32.toUInt64 <<< ((32 : UInt64) % 64) |||
      errPack p >>> ((8 : UInt64) % 64) <<< ((8 : UInt64) % 64) &&& (65280 : UInt64)) = errPack p := by
  simp only [errPack, toUInt32_toUInt64]
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 655's result: `Ok` with the byte at `i` and the reader past it, or `Err(box)` at the end. -/
def res655 (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat) (de ptr : UInt32) (bs : List UInt8)
    (i : Nat) (rs : List Value) : IProp GF :=
  if h : i < bs.length then
    iprop(⌜rs = [.i64 (okPack de bs[i])]⌝ ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs (i + 1))
  else
    iprop(∃ p : UInt32, ⌜rs = [.i64 (errPack p)] ∧ p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗ rd n de ptr bs i)

/-- The code `next_or_eof` runs (persistent). -/
def eofCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(errCode n maxP inst mi A ∗ A 637 ↪[wf] FuncInst.wasm types[11]! inst f637 ∗
    A 656 ↪[wf] FuncInst.wasm types[30]! inst f656 ∗ A 654 ↪[wf] FuncInst.wasm types[30]! inst f654 ∗
    A 655 ↪[wf] FuncInst.wasm types[11]! inst f655 ∗ A 653 ↪[wf] FuncInst.wasm types[11]! inst f653)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (eofCode (GF := GF) n maxP inst mi A) := by
  unfold eofCode SerdeErrBox.errCode; infer_instance

end Defs

section L655

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`next_or_eof(rd)`** (655): `res655`, at most `costErr cfg F i` and a constant. -/
theorem f655_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat) (maxP mlen : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat)
    (hr : roomFor4 mlen maxP 20) :
    eofCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f655 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i))
        (fun _ => 150 * cfg.regularOpCost + costErr cfg F i)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          res655 n maxP mlen live F de ptr bs i rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold eofCode at Hk'
  icases Hk' with ⟨#HE, #H637, #H656, -, -, -⟩
  ihave #HE' := HE
  iunfold errCode at HE'
  icases HE' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha637 := hm.funcs 637 (by decide)
  have ha656 := hm.funcs 656 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t30 : types[30]!.params.length = 2 := by rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hrd⟩
  subst hargs
  generalize hE : costErr cfg F i = E
  rw [show 150 * cfg.regularOpCost + E + R = 150 * cfg.regularOpCost + (E + R) by omega]
  simp only [f655]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeRead.f637_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn Cg de ptr bs i hi
    (by omega) hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok : Numeric.bool (optByte bs[i]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  by_cases hil : i < bs.length
  · have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hil
    rw [hb] at hok ⊢
    have hz : Numeric.bool (Numeric.irelop64 IRelOp.eq (optByte (some bs[i]) &&& 256) 0) = 0 := by
      generalize bs[i] = b; revert b; exact SerdeRead.uint8_forall (by decide +kernel)
    repeat mstep
    mstep [Hg]
    rw [show sp - 16 + 16 = sp by simp]
    repeat mstep
    mcredits R
    iframe Hc Hg Hs Hvt
    simp only [res655, dif_pos hil, htype, Nat.sub_self, List.drop_zero, okPack_eq]
    iframe Hinv
    rw [show min (i + 1) bs.length = i + 1 by omega]
    iexact Hrd
  · have hib : i = bs.length := by omega
    have hb : bs[i]? = none := by rw [hib]; simp
    rw [hb] at hok ⊢
    rw [show min (i + 1) bs.length = i by omega]
    icases stk_split n (sp.toNat - 96) 80 16 $$ Hs with ⟨Lo, Fr⟩
    icases stk_split n (sp.toNat - 96 + 80) 4 12 $$ Fr with ⟨C0, C4⟩
    icases stk_split n (sp.toNat - 96 + 80 + 4) 8 4 $$ C4 with ⟨C4, U⟩
    iunfold stk at C0 C4
    icases C0 with ⟨%c0, %hc0, C0⟩
    icases C4 with ⟨%c4, %hc4, C4⟩
    ihave C0 := memBytes_addr (show sp.toNat - 96 + 80 = (sp - 16).toNat by omega) $$ C0
    repeat mstep
    mstep [C0]
    repeat mstep
    ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 4) c4 (by simp) $$ [C0 C4]
    · ihave C4 := memBytes_addr (show sp.toNat - 96 + 80 + 4 = (sp - 16).toNat + 4 by omega) $$ C4
      iframe C0 C4
    have key := f654_spec (GF := GF) cfg lim (d + 1) types[30]! rfl inst mi A n g ta hm (by omega) Cg gt (sp - 16)
      de (sp - 16) ptr idx (bytes32 4 ++ c4) bs i maxP mlen live F (by simp; omega) (by omega) hde hi hlen hptr
      (by omega) hr
    rw [← f656_eq, hE] at key
    ihave #S656 := key $$ HE
    ihave Lo := stk_addr (show sp.toNat - 96 = (sp - 16).toNat - 80 by omega) $$ Lo
    mcall S656 using [Hg Lo Hvt Hinv C Hrd]
    · iframe Hg Lo Hvt Hinv C Hrd
    icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, Lo, Hvt, HA, C, Hrd⟩
    subst hrs
    repeat mstep
    mstep [Hg]
    rw [show sp - 16 + 16 = sp by simp]
    repeat mstep
    mcredits R
    iframe Hc Hg Hvt
    simp only [res655, dif_neg hil, htype, Nat.sub_self, List.drop_zero, errPack_repack]
    isplitr [HA Hrd]
    · ihave Lo := stk_addr (show (sp - 16).toNat - 80 = sp.toNat - 96 by omega) $$ Lo
      ihave C := stk_intro n _ _ $$ C
      rw [show (bytes32 4 ++ c4).length = 12 by simp [bytes32]; omega]
      ihave C := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ C
      ihave C := stk_join n (sp.toNat - 96 + 80) 12 4 $$ [C U]
      · iframe C
        iapply stk_addr (show sp.toNat - 96 + 80 + 4 + 8 = sp.toNat - 96 + 80 + 12 by omega) $$ U
      iapply stk_join n (sp.toNat - 96) 80 16
      iframe Lo C
    iexists p
    iframe HA Hrd
    ipureintro; exact ⟨rfl, hp0⟩

end L655

end WNear.Binary.SerdeEsc
