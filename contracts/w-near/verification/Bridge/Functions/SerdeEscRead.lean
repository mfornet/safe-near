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

/-! ## `decode_hex_escape` (653) -/

open NearInterface.Json (hexValue hex4)

/-- The table of hex digits at 1062712: the digit's value, 255 for any other byte. -/
def hexTable : List UInt8 :=
  (List.range 256).map fun k => match hexValue (UInt8.ofNat k) with | some v => UInt8.ofNat v | none => 255

set_option maxRecDepth 100000 in
/-- The table is the data segment's bytes at 1062712. -/
theorem hexData_segment :
    (List.range 256).map (fun k => wNearSource.read (159306 + (1062712 - 1048576) + k)) = hexTable := by
  decide +kernel

theorem hexTable_length : hexTable.length = 256 := by simp [hexTable]

set_option maxRecDepth 100000 in
theorem hex_at (b : UInt8) :
    (hexTable[b.toNat]'(by rw [hexTable_length]; exact b.toNat_lt)).toUInt32 =
      match hexValue b with | some v => UInt32.ofNat v | none => 255 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem hexValue_lt (b : UInt8) (v : Nat) (h : hexValue b = some v) : v < 16 := by
  have key : ∀ b : UInt8, (hexValue b).getD 0 < 16 := SerdeRead.uint8_forall (by decide +kernel)
  have := key b
  rw [h] at this
  exact this

/-- The value of the hex digits `l`, if they all are. -/
def hexAcc (l : List UInt8) : Option Nat :=
  l.foldl (fun acc b => acc.bind fun a => (hexValue b).map (a * 16 + ·)) (some 0)

theorem hexAcc_snoc (l : List UInt8) (b : UInt8) :
    hexAcc (l ++ [b]) = (hexAcc l).bind fun a => (hexValue b).map (a * 16 + ·) := by
  simp [hexAcc, List.foldl_append]

theorem hexAcc_lt (l : List UInt8) (a : Nat) (h : hexAcc l = some a) : a < 16 ^ l.length := by
  induction l using List.reverseRecOn generalizing a with
  | nil => simp [hexAcc] at h; subst h; simp
  | append_singleton l b ih =>
    rw [hexAcc_snoc] at h
    cases ha : hexAcc l with
    | none => rw [ha] at h; simp at h
    | some a' =>
      rw [ha] at h
      cases hb : hexValue b with
      | none => rw [hb] at h; simp at h
      | some v =>
        rw [hb] at h; simp at h
        have := ih a' ha
        have := hexValue_lt b v hb
        subst h
        rw [List.length_append, List.length_singleton, Nat.pow_succ]
        have : (a' + 1) * 16 ≤ 16 ^ l.length * 16 := Nat.mul_le_mul_right 16 (by omega)
        omega

theorem hexAcc_append_none (l m : List UInt8) (h : hexAcc l = none) : hexAcc (l ++ m) = none := by
  induction m using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton m b ih => rw [← List.append_assoc, hexAcc_snoc, ih]; rfl

theorem hex4_eq (l : List UInt8) :
    hex4 l = if 4 ≤ l.length then (hexAcc (l.take 4)).map (·, l.drop 4) else none := by
  match l with
  | [] | [_] | [_, _] | [_, _, _] => simp [hex4]
  | a :: b :: c :: d :: rest =>
    simp only [hex4, List.length_cons, show 4 ≤ rest.length + 1 + 1 + 1 + 1 by omega, ite_true,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, hexAcc, List.foldl_cons,
      List.foldl_nil]
    cases hexValue a <;> cases hexValue b <;> cases hexValue c <;> cases hexValue d <;> simp <;> omega

theorem shl4_mask (a v : Nat) (ha : a < 4096) (hv : v < 16) :
    (UInt32.ofNat a <<< (4 % 32) &&& 65520) + UInt32.ofNat v = UInt32.ofNat (a * 16 + v) := by
  apply UInt32.toNat_inj.mp
  have h1 : (UInt32.ofNat a <<< (4 % 32) &&& 65520).toNat = a * 16 := by
    have e : (UInt32.ofNat a <<< (4 % 32)).toNat = a * 16 := by
      simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    rw [UInt32.toNat_and, e]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    rw [show (65520 : UInt32).toNat = 65520 from rfl]
    rw [show a * 16 = a * 2 ^ 4 by norm_num, Nat.testBit_mul_two_pow]
    by_cases hj : j < 4
    · simp [hj]
    by_cases hj2 : j < 16
    · have : (65520 : Nat).testBit j = true := by interval_cases j <;> decide
      simp [this]
    · have : a.testBit (j - 4) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (by
        calc 4096 = 2 ^ 12 := by norm_num
          _ ≤ 2 ^ (j - 4) := Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this]
  rw [UInt32.toNat_add, h1]
  simp

/-- The packed `Ok(n)` of 653. -/
def hexPack (v : Nat) : UInt64 := UInt64.ofNat v <<< 16

theorem costErr_mono' (cfg : WasmConfig) (F i j : Nat) (h : i ≤ j) :
    costErr cfg F i ≤ costErr cfg F j := by
  unfold costErr SerdePosition.cost638 SerdePosition.cost645
  have := Nat.mul_le_mul_right cfg.regularOpCost (show 80 + (40 + (200 + 50 * i)) ≤ 80 + (40 + (200 + 50 * j)) by omega)
  omega

theorem errPack_repack653 (p : UInt32) :
    (((errPack p >>> ((16 : UInt64) % 64)).toUInt32.toUInt64 &&& (65535 : UInt64)) <<< ((16 : UInt64) % 64) |||
      errPack p &&& (18446744069414584320 : UInt64) ||| errPack p &&& (65535 : UInt64)) = errPack p := by
  simp only [errPack, toUInt32_toUInt64]
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

theorem hexPack_eq (acc : Nat) (h : acc < 65536) :
    (((UInt32.ofNat acc).toUInt64 &&& (65535 : UInt64)) <<< ((16 : UInt64) % 64) ||| 0 ||| (0 : UInt64) &&& 65535) =
      hexPack acc := by
  have e : (UInt32.ofNat acc).toUInt64 &&& (65535 : UInt64) = UInt64.ofNat acc := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (65535 : UInt64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp; omega
  rw [e]; simp [hexPack]

section Defs653

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 653's result: `Ok(n)` on four hex digits, the reader past them, or `Err(box)`. -/
def res653 (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat) (de ptr : UInt32) (bs : List UInt8)
    (i : Nat) (rs : List Value) : IProp GF :=
  match hex4 (bs.drop i) with
  | some (v, _) => iprop(⌜rs = [.i64 (hexPack v)]⌝ ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs (i + 4))
  | none => iprop(∃ (p : UInt32) (j : Nat), ⌜rs = [.i64 (errPack p)] ∧ p ≠ 0 ∧ j ≤ bs.length⌝ ∗
      heapA n maxP mlen live F 20 p ∗ rd n de ptr bs j)

/-- 653's loop: `k` digits read, their value `acc`. -/
def inv653 (n inst : Nat) (mi : ModuleInst) (Cg c₀ K R : Nat) (de s : UInt32) (bs : List UInt8) (i : Nat)
    (ptr : UInt32) (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k acc : Nat) (l9 l10 : UInt32), ⌜X = [] ∧
      g = ⟨#[.i32 de, .i32 s, .i32 (UInt32.ofNat i), .i32 (UInt32.ofNat k), .i32 (UInt32.ofNat bs.length),
        .i32 (ptr + UInt32.ofNat i), .i32 (UInt32.ofNat acc), .i64 0, .i64 0, .i32 l9, .i32 l10], inst, mi⟩ ∧
      k ≤ 4 ∧ hexAcc ((bs.drop i).take k) = some acc⌝ ∗
    credits Cg ((4 - k) * 50 * c₀ + K + R) ∗ n ↦[i32][ de.toNat + 8 ] UInt32.ofNat (i + k) ∗ P)

end Defs653

section L653

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`decode_hex_escape(rd)`** (653): `res653`. -/
theorem f653_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat) (maxP mlen : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 8 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 96 ≤ sp.toNat)
    (hr : roomFor4 mlen maxP 20) :
    eofCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f653 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i ∗ n ↦[wms][ 1062712 ] hexTable))
        (fun _ => 300 * cfg.regularOpCost + costErr cfg F bs.length)
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
  generalize hE : costErr cfg F bs.length = E
  rw [show 300 * cfg.regularOpCost + E + R = 300 * cfg.regularOpCost + (E + R) by omega]
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
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 240 * cfg.regularOpCost + (E + R))
      (I := inv653 n inst mi Cg cfg.regularOpCost (40 * cfg.regularOpCost) (E + R) de (sp - 16) bs i ptr
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
        rw [show (4 - k) * 50 * cfg.regularOpCost + 40 * cfg.regularOpCost + (E + R) =
          50 * cfg.regularOpCost + ((4 - (k + 1)) * 50 * cfg.regularOpCost + 40 * cfg.regularOpCost + (E + R)) by
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
          have hE1 := costErr_mono' cfg F (i + (k + 1)) bs.length (by omega)
          rw [hE] at hE1
          dsimp only
          mstep; mstep; mstep; mstep
          simp only [Post.mloop]
          mctrl_norm
          repeat mpay
          repeat mstep
          mstep [C0]
          repeat mstep
          ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 11) c4 (by simp) $$ [C0 C4]
          · iframe C0 C4
          have key := f654_spec (GF := GF) cfg lim (d + 1) types[30]! rfl inst mi A n g ta hm (by omega) Cg gt (sp - 16)
            de (sp - 16) ptr idx (bytes32 11 ++ c4) bs (i + (k + 1)) maxP mlen live F (by simp; omega) (by omega) hde
            (by omega) (by omega) hptr (by omega) hr
          generalize hE2 : costErr cfg F (i + (k + 1)) = E2 at key hE1
          ihave #S654 := key $$ HE
          rw [show Z + 40 * cfg.regularOpCost + (E + R) = Z + 40 * cfg.regularOpCost + (E2 + (E - E2 + R)) by omega]
          mcall S654 using [Hg Lo Hvt Hinv C D0 D4 D8 Hb]
          · iframe Hg Lo Hvt Hinv C
            iunfold rd, ArgsLeaves.sliceRead
            iframe D0 D4 D8 Hb
          icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, Lo, Hvt, HA, C, Hrd⟩
          subst hrs
          repeat mstep
          mstep [Hg]
          rw [show sp - 16 + 16 = sp by simp]
          repeat mstep
          mcredits R
          iframe Hc Hg Hvt Ht
          simp only [res653, hx, htype, Nat.sub_self, List.drop_zero, errPack_repack653]
          isplitr [HA Hrd]
          · ihave Lo := stk_addr (show (sp - 16).toNat - 80 = sp.toNat - 96 by omega) $$ Lo
            ihave C := stk_intro n _ _ $$ C
            rw [show (bytes32 11 ++ c4).length = 12 by simp [bytes32]; omega]
            ihave C := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ C
            ihave C := stk_join n (sp.toNat - 96 + 80) 12 4 $$ [C U]
            · iframe C
              iapply stk_addr (show sp.toNat - 96 + 80 + 4 + 8 = sp.toNat - 96 + 80 + 12 by omega) $$ U
            iapply stk_join n (sp.toNat - 96) 80 16
            iframe Lo C
          iexists p, i + (k + 1)
          iframe HA Hrd
          ipureintro; exact ⟨rfl, hp0, by omega⟩
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
  · have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat i + 4) (UInt32.ofNat bs.length)) = 1 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hi4, hlu]; omega
    have hx : hex4 (bs.drop i) = none := by rw [hex4_eq]; simp; omega
    repeat mstep
    mstep [D8]
    repeat mstep
    mstep [C0]
    repeat mstep
    ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 4) c4 (by simp) $$ [C0 C4]
    · iframe C0 C4
    have key := f654_spec (GF := GF) cfg lim (d + 1) types[30]! rfl inst mi A n g ta hm (by omega) Cg gt (sp - 16)
      de (sp - 16) ptr idx (bytes32 4 ++ c4) bs bs.length maxP mlen live F (by simp; omega) (by omega) hde
      (Nat.le_refl _) (by omega) hptr (by omega) hr
    rw [hE] at key
    ihave #S654 := key $$ HE
    mcall S654 using [Hg Lo Hvt Hinv C D0 D4 D8 Hb]
    · iframe Hg Lo Hvt Hinv C
      iunfold rd, ArgsLeaves.sliceRead
      iframe D0 D4 D8 Hb
    icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, Lo, Hvt, HA, C, Hrd⟩
    subst hrs
    repeat mstep
    mstep [Hg]
    rw [show sp - 16 + 16 = sp by simp]
    repeat mstep
    mcredits R
    iframe Hc Hg Hvt Ht
    simp only [res653, hx, htype, Nat.sub_self, List.drop_zero, errPack_repack653]
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
    iexists p, bs.length
    iframe HA Hrd
    ipureintro; exact ⟨rfl, hp0, Nat.le_refl _⟩

end L653

end WNear.Binary.SerdeEsc
