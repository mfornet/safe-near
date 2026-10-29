import Bridge.Functions.EncodeUtf8
import Bridge.Functions.EscModel
import Bridge.Functions.ScratchGrow

/-!
# `parse_escape` (649) (M6)

After a `\` in a string, `parse_str` (646) calls `parse_escape(rd, scratch)`:

```wat
;; 649 parse_escape(rd, scratch) → box (0: Ok)   frame 32
;;   e := next_or_eof(rd) (655)                    EOF ⇒ its error
;;   " \ / b f n r t ⇒ push the byte (614)
;;   u ⇒ n := decode_hex_escape(rd) (653)
;;        n ∈ DC00..DFFF ⇒ error 17 (a lone trailing surrogate)
;;        n ∈ D800..DBFF ⇒ next_or_eof = '\', next_or_eof = 'u' (else error 20),
;;                         m := 653, m ∈ DC00..DFFF (else error 17),
;;                         c := 0x10000 + (n - D800)·0x400 + (m - DC00)
;;        else c := n
;;        encode_utf8(c) (605) into a 4-byte buffer, appended (613)
;;   else ⇒ error 11 (InvalidEscape)
```

serde_json 1.0.60 rejects a lone or reversed surrogate, as the model's `unicodeEscape` does: the
outcome is `escDecode`, the model's escape on the bytes after the `\`.

* `escDecode`: the decoded bytes and the number of bytes read, or `none`.
* `f649_spec`: `res649`, `0` with the bytes appended to the scratch, or a box.
-/

namespace WNear.Binary.ParseEscape

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open NearInterface.Json (hexValue hex4 unicodeEscape)
open WNear.Binary.EncodeUtf8 (enc605 enc605_eq)

theorem ue_none (rest : List UInt8) (h : hex4 rest = none) : unicodeEscape rest = none := by
  simp [unicodeEscape, h]

theorem ue_lo (rest r : List UInt8) (n : Nat) (h : hex4 rest = some (n, r)) (hn : 0xDC00 ≤ n ∧ n < 0xE000) :
    unicodeEscape rest = none := by
  simp only [unicodeEscape, h, Option.bind_eq_bind, Option.bind_some]
  rw [if_neg (by simp; omega), if_pos (by simp; omega)]

theorem ue_bmp (rest r : List UInt8) (n : Nat) (h : hex4 rest = some (n, r))
    (hn : n < 0xD800 ∨ (0xE000 ≤ n ∧ n < 0x10000)) :
    unicodeEscape rest = some (Char.ofNat n, r) := by
  simp only [unicodeEscape, h, Option.bind_eq_bind, Option.bind_some]
  rw [if_neg (by simp; omega), if_neg (by simp; omega), if_pos (by simp [Nat.isValidChar]; omega)]
  rfl

theorem ue_hi_nobs (rest r : List UInt8) (n : Nat) (h : hex4 rest = some (n, r)) (hn : 0xD800 ≤ n ∧ n < 0xDC00)
    (hr : ∀ r2, r ≠ 0x5C :: 0x75 :: r2) : unicodeEscape rest = none := by
  simp only [unicodeEscape, h, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by simp; omega)]
  all_goals (try split) <;> (try simp_all)

theorem ue_hi (rest r r2 : List UInt8) (n : Nat) (h : hex4 rest = some (n, r)) (hn : 0xD800 ≤ n ∧ n < 0xDC00)
    (hr : r = 0x5C :: 0x75 :: r2) :
    unicodeEscape rest = (hex4 r2).bind fun (m, r3) =>
      if 0xDC00 ≤ m ∧ m < 0xE000 then some (Char.ofNat (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)), r3)
      else none := by
  subst hr
  simp only [unicodeEscape, h, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by simp; omega)]
  cases h2 : hex4 r2 with
  | none => simp
  | some p =>
    obtain ⟨m, r3⟩ := p
    simp only [Option.bind_some]
    by_cases hm : 0xDC00 ≤ m ∧ m < 0xE000
    · rw [if_pos (by simp; omega), if_pos hm, if_pos (by simp [Nat.isValidChar]; omega)]; rfl
    · rw [if_neg (by simp; omega), if_neg hm]

/-! ## The code's tests on a 16-bit `n` -/

theorem and_hi (n k : Nat) (hk : k ≤ 16) (hn : n < 2 ^ 16) :
    n &&& ((2 ^ (16 - k) - 1) * 2 ^ k) = n / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hj : k ≤ j
  · rw [show j - k + k = j by omega]
    by_cases hj2 : j < 16
    · simp [hj, show j - k < 16 - k by omega]
    · have : n.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hj]

theorem errPack_bit (p : UInt32) : Numeric.bool (WNear.Binary.SerdeErrBox.errPack p &&& 1 == 0) = 0 := by
  have : WNear.Binary.SerdeErrBox.errPack p &&& 1 = 1 := by
    simp only [WNear.Binary.SerdeErrBox.errPack]
    apply UInt64.toBitVec_inj.mp
    ext i hi
    simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
    interval_cases i <;> simp (config := {decide := true})
  simp [Numeric.bool, this]

theorem okPack_bit (de : UInt32) (b : UInt8) :
    Numeric.bool (WNear.Binary.SerdeEsc.okPack de b &&& 1 == 0) = 1 := by
  have : WNear.Binary.SerdeEsc.okPack de b &&& 1 = 0 := by
    simp only [WNear.Binary.SerdeEsc.okPack]
    apply UInt64.toBitVec_inj.mp
    ext i hi
    simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
    interval_cases i <;> simp (config := {decide := true})
  simp [Numeric.bool, this]

theorem okPack_byte (de : UInt32) (b : UInt8) :
    ((WNear.Binary.SerdeEsc.okPack de b).toUInt32 >>> ((8 : UInt32) % 32) &&& (255 : UInt32)) = b.toUInt32 := by
  simp only [WNear.Binary.SerdeEsc.okPack]
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

theorem errPack_box (p : UInt32) :
    (WNear.Binary.SerdeErrBox.errPack p >>> ((32 : UInt64) % 64)).toUInt32 = p := by
  simp only [WNear.Binary.SerdeErrBox.errPack]
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  interval_cases i <;> simp (config := {decide := true})

open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4 errPack)
open WNear.Binary.SerdeEsc (eofCode okPack res655 res653 hexTable hexPack f655_spec f653_spec costErr_mono')
open WNear.Binary.ScratchGrow (sbuf sgCode capAfter fAfter hlAfter roomRes costExt costApp)

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The scratch's buffer with the error box allocated after it (`sbuf`, `heapA` for `heapInv`). -/
def sbufE (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ptr cap : UInt32) (bs : List UInt8)
    (p : UInt32) : IProp GF :=
  iprop(⌜bs.length ≤ cap.toNat ∧ ptr ≠ 0 ∧ ptr.toNat + cap.toNat < 2 ^ 32 ∧ (cap = 0 → ptr = 1)⌝ ∗
    n ↦[wms][ ptr.toNat ] bs ∗
    (∃ junk : List UInt8, ⌜junk.length = cap.toNat - bs.length⌝ ∗ n ↦[wms][ ptr.toNat + bs.length ] junk) ∗
    heapA n maxP hl (if cap = 0 then live else (ptr.toNat, cap.toNat) :: live) F 20 p)

/-- The scratch's buffer without its heap. -/
def sbufR (n : Nat) (ptr cap : UInt32) (bs : List UInt8) : IProp GF :=
  iprop(⌜bs.length ≤ cap.toNat ∧ ptr ≠ 0 ∧ ptr.toNat + cap.toNat < 2 ^ 32 ∧ (cap = 0 → ptr = 1)⌝ ∗
    n ↦[wms][ ptr.toNat ] bs ∗
    (∃ junk : List UInt8, ⌜junk.length = cap.toNat - bs.length⌝ ∗ n ↦[wms][ ptr.toNat + bs.length ] junk))

theorem sbuf_split {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {ptr cap : UInt32} {bs : List UInt8} :
    sbuf (GF := GF) n maxP hl live F ptr cap bs ⊢
      heapInv n maxP hl (if cap = 0 then live else (ptr.toNat, cap.toNat) :: live) F ∗ sbufR n ptr cap bs := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%h, Hb, Hj, Hinv⟩
  iframe Hinv
  iunfold sbufR
  iframe Hb Hj
  ipureintro; exact h

theorem sbuf_join {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {ptr cap : UInt32} {bs : List UInt8} :
    heapInv n maxP hl (if cap = 0 then live else (ptr.toNat, cap.toNat) :: live) F ∗ sbufR n ptr cap bs ⊢
      sbuf (GF := GF) n maxP hl live F ptr cap bs := by
  iintro ⟨Hinv, H⟩
  iunfold sbufR at H
  icases H with ⟨%h, Hb, Hj⟩
  iunfold sbuf
  iframe Hinv Hb Hj
  ipureintro; exact h

theorem sbufE_intro {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {ptr cap : UInt32} {bs : List UInt8}
    {p : UInt32} :
    heapA n maxP hl (if cap = 0 then live else (ptr.toNat, cap.toNat) :: live) F 20 p ∗ sbufR n ptr cap bs ⊢
      sbufE (GF := GF) n maxP hl live F ptr cap bs p := by
  iintro ⟨HA, H⟩
  iunfold sbufR at H
  icases H with ⟨%h, Hb, Hj⟩
  iunfold sbufE
  iframe HA Hb Hj
  ipureintro; exact h

/-- The code `parse_escape` runs (persistent). -/
def escCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(sgCode n maxP inst mi A ∗ eofCode n maxP inst mi A ∗
    A 651 ↪[wf] FuncInst.wasm types[13]! inst f651 ∗ A 605 ↪[wf] FuncInst.wasm types[31]! inst f605 ∗
    A 649 ↪[wf] FuncInst.wasm types[13]! inst f649)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (escCode (GF := GF) n maxP inst mi A) := by
  unfold escCode; infer_instance

/-- 649's result: `0` with the escape's bytes appended to the scratch and the reader past the escape,
or a box, the scratch unchanged. -/
def res649 (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (de ptr : UInt32) (bs : List UInt8)
    (j : Nat) (sc ptrS capS : UInt32) (acc : List UInt8) (rs : List Value) : IProp GF :=
  match escDecode (bs.drop j) with
  | some (out, m) => iprop(⌜rs = [.i32 0]⌝ ∗ rd n de ptr bs (j + m) ∗
      ∃ (p : UInt32) (hl' : Nat),
        ⌜hlAfter hl hl' capS (UInt32.ofNat acc.length) (UInt32.ofNat out.length)⌝ ∗
        n ↦[i32][ sc.toNat ] p ∗
        n ↦[i32][ sc.toNat + 4 ] capAfter capS (UInt32.ofNat acc.length) (UInt32.ofNat out.length) ∗
        n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat (acc.length + out.length) ∗
        sbuf n maxP hl' live (fAfter F capS (UInt32.ofNat acc.length) (UInt32.ofNat out.length)) p
          (capAfter capS (UInt32.ofNat acc.length) (UInt32.ofNat out.length)) (acc ++ out))
  | none => iprop(∃ (p : UInt32) (j' : Nat), ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ j' ≤ bs.length⌝ ∗
      rd n de ptr bs j' ∗ n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
      n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbufE n maxP hl live F ptrS capS acc p)

end Defs

/-- 649's cost: the reads, two hex decodes and three errors at most, and the append. -/
def cost649 (cfg : WasmConfig) (F : Nat) (capS : UInt32) (acc bs : List UInt8) (j : Nat) : Nat :=
  3000 * cfg.regularOpCost + 8 * costErr cfg F bs.length +
    costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))

set_option maxRecDepth 100000 in
theorem tab1 (b : UInt8) :
    ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[(b.toUInt32 + 4294967186).toNat]?.getD 0 =
      if b = 110 then 7 else if b = 114 then 8 else if b = 116 then 9 else if b = 117 then 10
      else if b = 111 ∨ b = 112 ∨ b = 113 ∨ b = 115 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem tab2 (b : UInt8) :
    ([5, 1, 1, 1, 6] : List Nat)[(b.toUInt32 + 4294967198).toNat]?.getD 0 =
      if b = 98 then 5 else if b = 102 then 6 else if b = 99 ∨ b = 100 ∨ b = 101 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem errPack_bit16 (p : UInt32) :
    Numeric.bool (WNear.Binary.SerdeErrBox.errPack p &&& 65535 == 0) = 0 := by
  have : WNear.Binary.SerdeErrBox.errPack p &&& 65535 = 1 := by
    simp only [WNear.Binary.SerdeErrBox.errPack]
    apply UInt64.toBitVec_inj.mp
    ext i hi
    simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
    interval_cases i <;> simp (config := {decide := true})
  simp [Numeric.bool, this]

theorem hexPack_toNat (nv : Nat) (h : nv < 65536) : (WNear.Binary.SerdeEsc.hexPack nv).toNat = nv * 65536 := by
  simp only [WNear.Binary.SerdeEsc.hexPack, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  rw [show (16 : UInt64).toNat % 64 = 16 from rfl, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem hexPack_low (nv : Nat) (h : nv < 65536) :
    Numeric.bool (WNear.Binary.SerdeEsc.hexPack nv &&& 65535 == 0) = 1 := by
  have : WNear.Binary.SerdeEsc.hexPack nv &&& 65535 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (65535 : UInt64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      hexPack_toNat nv h]
    simp
  simp [Numeric.bool, this]

theorem hexPack_val (nv : Nat) (h : nv < 65536) :
    (WNear.Binary.SerdeEsc.hexPack nv >>> ((16 : UInt64) % 64)).toUInt32 = UInt32.ofNat nv := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hexPack_toNat nv h]
  rw [show ((16 : UInt64) % 64).toNat % 64 = 16 from rfl, Nat.shiftRight_eq_div_pow]
  simp

theorem mask10 (nv : Nat) (h : nv < 65536) : UInt32.ofNat nv &&& 64512 = UInt32.ofNat (nv / 1024 * 1024) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
    show (64512 : UInt32).toNat = (2 ^ (16 - 10) - 1) * 2 ^ 10 from rfl, and_hi nv 10 (by decide) h]
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

theorem mask11 (nv : Nat) (h : nv < 65536) : UInt32.ofNat nv &&& 63488 = UInt32.ofNat (nv / 2048 * 2048) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
    show (63488 : UInt32).toNat = (2 ^ (16 - 11) - 1) * 2 ^ 11 from rfl, and_hi nv 11 (by decide) h]
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

theorem eq_ofNat (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat a) (UInt32.ofNat b)) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp [Numeric.bool, Numeric.irelop32]
  · rw [if_neg h]
    have : UInt32.ofNat a ≠ UInt32.ofNat b := fun e => h (by
      have := congrArg UInt32.toNat e; simp at this; omega)
    simp [Numeric.bool, Numeric.irelop32, this]

theorem eqc (a : Nat) (k : UInt32) (ha : a < 2 ^ 32) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat a) k) = if a = k.toNat then 1 else 0 := by
  by_cases h : a = k.toNat
  · rw [if_pos h]
    have : UInt32.ofNat a = k := by apply UInt32.toNat_inj.mp; simp; omega
    simp [Numeric.bool, Numeric.irelop32, this]
  · rw [if_neg h]
    have : UInt32.ofNat a ≠ k := fun e => h (by rw [← e]; simp; omega)
    simp [Numeric.bool, Numeric.irelop32, this]

theorem and_hiw (n k w : Nat) (hk : k ≤ w) (hn : n < 2 ^ w) :
    n &&& ((2 ^ (w - k) - 1) * 2 ^ k) = n / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hj : k ≤ j
  · rw [show j - k + k = j by omega]
    by_cases hj2 : j < w
    · simp [hj, show j - k < w - k by omega]
    · have : n.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hj]

theorem okPack_ff00 (de : UInt32) (b : UInt8) :
    WNear.Binary.SerdeEsc.okPack de b &&& (65280 : UInt64) = b.toUInt64 <<< (8 : UInt64) := by
  simp only [WNear.Binary.SerdeEsc.okPack]
  apply UInt64.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

set_option maxRecDepth 100000 in
theorem t5c (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.eq (b.toUInt64 <<< (8 : UInt64)) 23552) = if b = 92 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem t75 (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.eq (b.toUInt64 <<< (8 : UInt64)) 29952) = if b = 117 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem and16 (a : Nat) (h : a < 65536) : UInt32.ofNat a &&& 65535 = UInt32.ofNat a := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem sub_k (a k : Nat) (c : UInt32) (h : k ≤ a) (ha : a < 65536) (hc : c.toNat + k = 2 ^ 32) :
    (UInt32.ofNat a &&& 65535) + c = UInt32.ofNat (a - k) := by
  rw [and16 a ha]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add]; simp; omega

theorem ne16 (a : Nat) (h : a < 65536) :
    Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat a &&& 65535) (UInt32.ofNat a)) = 0 := by
  rw [and16 a h]; simp [Numeric.bool, Numeric.irelop32]

theorem raw_eq (a b : Nat) (ha : a < 1024) (hb : b < 1024) :
    ((UInt32.ofNat a &&& 65535) <<< ((10 : UInt32) % 32) ||| (UInt32.ofNat b &&& 65535)) = UInt32.ofNat (a * 1024 + b) := by
  rw [and16 a (by omega), and16 b (by omega)]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft]
  simp only [UInt32.toNat_ofNat', show ((10 : UInt32) % 32).toNat % 32 = 10 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 32), Nat.mod_eq_of_lt (by omega : b < 2 ^ 32),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : a * 2 ^ 10 < 2 ^ 32), Nat.mod_eq_of_lt (by omega : a * 1024 + b < 2 ^ 32)]
  rw [show a * 1024 + b = 2 ^ 10 * a + b by omega, Nat.two_pow_add_eq_or_of_lt (by omega : b < 2 ^ 10), Nat.mul_comm]

theorem mask27 (cp : Nat) (h1 : 65536 ≤ cp) (h2 : cp < 2 ^ 27) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat cp &&& 134215680) 55296) = 0 := by
  have e : UInt32.ofNat cp &&& 134215680 = UInt32.ofNat (cp / 2 ^ 11 * 2 ^ 11) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and, UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
      show (134215680 : UInt32).toNat = (2 ^ (27 - 11) - 1) * 2 ^ 11 from rfl, and_hiw cp 11 27 (by decide) h2]
    rw [Nat.mod_eq_of_lt (by have := Nat.div_mul_le_self cp (2 ^ 11); omega)]
  rw [e, eqc _ _ (by have := Nat.div_mul_le_self cp (2 ^ 11); omega)]
  rw [if_neg]
  intro h
  have : (55296 : UInt32).toNat = 55296 := rfl
  have := Nat.lt_div_mul_add (a := cp) (b := 2 ^ 11) (by decide)
  omega

theorem u8_ne (b c : UInt8) (h : b ≠ c) : Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 c.toUInt32) = 0 := by
  have : b.toUInt32 ≠ c.toUInt32 := fun e => h (by
    have := congrArg UInt32.toNat e; simp at this; exact UInt8.toNat_inj.mp this)
  simp [Numeric.bool, Numeric.irelop32, this]

theorem eqb (b : UInt8) (k : Nat) (hk : k < 256) :
    Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 (UInt32.ofNat k)) = if b.toNat = k then 1 else 0 := by
  by_cases h : b.toNat = k
  · subst h; simp [Numeric.bool, Numeric.irelop32]
  · rw [if_neg h]
    have : b.toUInt32 ≠ UInt32.ofNat k := fun e => h (by
      have := congrArg UInt32.toNat e; simp at this; omega)
    simp [Numeric.bool, Numeric.irelop32, this]

section L649

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option hygiene false in
/-- The decoded code point `cp` (in local 4) encoded (605) and appended (613), then `Ok`. Needs `hcp : cp <
0x110000`, `hd : escDecode (bs.drop j) = some (enc605 cp, _)` and the reader at `jr`. -/
local macro "enc649 " cp:term:max jr:term:max ep:term:max : tactic => `(tactic| (
  have hK1 : escK (bs.drop j) = (enc605 $cp).length := by simp [escK, hd]
  rw [hK1] at hX hr
  have hkl := EncodeUtf8.enc605_length $cp
  have hk4 : (enc605 $cp).length ≤ 4 := by rw [hkl]; split_ifs <;> omega
  icases stk_split n (s.toNat - 144 + 112) 8 24 $$ Fr with ⟨F0, F1⟩
  icases stk_split n (s.toNat - 144 + 112 + 8) 8 16 $$ F1 with ⟨OB, F2⟩
  icases stk_split n (s.toNat - 144 + 112 + 8 + 8) 4 12 $$ F2 with ⟨BF, F4⟩
  iunfold stk at OB BF
  icases OB with ⟨%ob, %hob, OB⟩
  icases BF with ⟨%bf, %hbf, BF⟩
  ihave BF := memBytes_addr (show s.toNat - 144 + 112 + 8 + 8 = (s - 32).toNat + 16 by omega) $$ BF
  mstep [BF]
  repeat mstep
  ihave OB := memBytes_addr (show s.toNat - 144 + 112 + 8 = (s - 32 + 8).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ OB
  ihave BF := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ BF
  mcall (EncodeUtf8.f605_spec cfg lim (d + 1) types[31]! rfl inst mi n hm.mem Cg (s - 32 + 8) (UInt32.ofNat $cp)
      (s - 32 + 16) ob (bytes32 0) hob (by simp [bytes32]) (by simp; omega)
      (by rw [UInt32.toNat_add, h32]; simp; omega) (by rw [UInt32.toNat_add, h32]; simp; omega)) using [OB BF]
  · iframe OB BF
  icases HQ with ⟨%hrs, O0, O4, BF⟩
  subst hrs
  rw [show (UInt32.ofNat $cp).toNat = $cp by simp; omega]
  ihave O0 := memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ O0
  ihave O4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 12 by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ O4
  mstep; mstep; mstep [O0]; mstep; mstep [O4]
  icases U128From.memBytes_split n (s - 32 + 16).toNat (enc605 $cp).length _ (by simp) $$ BF with ⟨B1, B2⟩
  rw [List.take_left' rfl]
  subst hL
  ihave Hsb := sbuf_join $$ [Hinv Hw]
  · iframe Hinv Hw
  ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
  ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
  · iframe L16 Lo
  have hkn : (UInt32.ofNat (enc605 $cp).length).toNat = (enc605 $cp).length := by simp; omega
  have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) sc (s - 32 + 16) (UInt32.ofNat (enc605 $cp).length) ptrS capS idx maxP hl live F acc (enc605 $cp)
    (by omega) (by omega) hcap (by omega) hkn.symm (by rw [UInt32.toNat_add, h32, hkn]; simp; omega) hr
  rw [hX] at key
  ihave #S613 := key $$ HG
  mcredits (900 * cfg.regularOpCost + ($ep + X + R))
  rw [show $ep + X + R = X + ($ep + R) by omega]
  mcall S613 using [Hg Lo Hvt S0 S4 S8 Hsb B1]
  · iframe Hg Lo Hvt S0 S4 S8 Hsb B1
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, S0, S4, S8, Hsb, B1⟩
  subst hrs
  mcredits (600 * cfg.regularOpCost + ($ep + R))
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Ht
  simp only [res649, hd, htype, Nat.sub_self, List.drop_zero]
  rw [show j + ($jr - j) = $jr by omega, hkn]
  isplitr [Hrd S0 S4 S8 Hsb]
  · ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
    ihave O0 := BorshFT.stkW (b := s.toNat - 144 + 112 + 8) _ (by omega) $$ O0
    ihave O4 := BorshFT.stkW (b := s.toNat - 144 + 112 + 8 + 4) _ (by omega) $$ O4
    ihave OB := stk_join n (s.toNat - 144 + 112 + 8) 4 4 $$ [O0 O4]
    · iframe O0 O4
    ihave B := U128From.memBytes_join n (s - 32 + 16).toNat (enc605 $cp).length _ _ rfl $$ [B1 B2]
    · iframe B1 B2
    ihave B := BorshFT.stkB (b := s.toNat - 144 + 112 + 8 + 8) (k := 4) _ (by rw [UInt32.toNat_add, h32]; simp; omega)
      (by simp [bytes32]; omega) $$ B
    ihave F2 := stk_join n (s.toNat - 144 + 112 + 8 + 8) 4 12 $$ [B F4]
    · iframe B F4
    ihave F1 := stk_join n (s.toNat - 144 + 112 + 8) 8 16 $$ [OB F2]
    · iframe OB F2
    ihave Fr := stk_join n (s.toNat - 144 + 112) 8 24 $$ [F0 F1]
    · iframe F0 F1
    iapply stk_join n (s.toNat - 144) 112 32
    iframe Lo Fr
  iframe Hrd
  iexists p, hl'
  iframe S0 S4 S8 Hsb
  ipureintro; exact hhl))

set_option hygiene false in
/-- The box of a callee's error (653 or 655) returned: `HA` the heap with it, the reader at `jr`, `hd` the
model's `none`. -/
local macro "boxret649 " jr:term:max : tactic => `(tactic| (
  repeat mstep
  rw [errPack_box]
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Ht
  simp only [res649, hd, htype, Nat.sub_self, List.drop_zero]
  isplitr [HA Hrd S0 S4 S8 Hw]
  · ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
    ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
    · iframe L16 Lo
    ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
    iapply stk_join n (s.toNat - 144) 112 32
    iframe Lo Fr
  iexists p, $jr
  iframe Hrd S0 S4 S8
  isplitr
  · ipureintro; exact ⟨rfl, hp0, by omega⟩
  subst hL
  iapply sbufE_intro
  iframe HA Hw))

set_option hygiene false in
/-- An error through 651 (= 325) with the code `c`, the reader at `i`; `hd` gives the model's `none`, and the
credits are `_ * c₀ + (ep + X + R)`. -/
local macro "err649 " c:term:max i:term:max ep:term:max : tactic => `(tactic| (
  have hEi := costErr_mono' cfg F $i bs.length (by omega)
  rw [hE] at hEi
  icases stk_split n (s.toNat - 144 + 112) 16 16 $$ Fr with ⟨F0, F1⟩
  icases stk_split n (s.toNat - 144 + 112 + 16) 12 4 $$ F1 with ⟨CB, F3⟩
  iunfold stk at CB
  icases CB with ⟨%cb, %hcb, CB⟩
  icases U128From.memBytes_split n _ 4 cb (by omega) $$ CB with ⟨C0, C4⟩
  ihave C0 := memBytes_addr (show s.toNat - 144 + 112 + 16 = (s - 32).toNat + 16 by omega) $$ C0
  icases stk_split n ((s - 32).toNat - 96) 16 80 $$ Lo with ⟨Lo16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 96 + 16 = (s - 32).toNat - 80 by omega) $$ Lo
  repeat mstep
  mstep [C0]
  ihave C := U128From.memBytes_join n ((s - 32).toNat + 16) 4 (bytes32 $c) (cb.drop 4) (by simp) $$ [C0 C4]
  · iframe C0
    iapply memBytes_addr (show s.toNat - 144 + 112 + 16 + 4 = (s - 32).toNat + 16 + 4 by omega) $$ C4
  ihave C := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ C
  have key := SerdeErrBox.f325_spec (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) de (s - 32 + 16) ptr idx (bytes32 $c ++ cb.drop 4) bs $i maxP hl L F (by simp; omega)
    (by rw [UInt32.toNat_add, h32]; simp; omega) hde (by omega) (by omega) hptr (by omega) hr4
  rw [← SerdeErrBox.f651_eq] at key
  generalize hEc : costErr cfg F $i = Ec at key hEi
  ihave #S651 := key $$ HErr
  mcredits (1000 * cfg.regularOpCost + ($ep + X + R))
  rw [show $ep + X + R = Ec + ($ep - Ec + X + R) by omega]
  mstep; mstep; mstep; mstep
  mcall S651 using [Hg Lo Hvt Hinv C Hrd]
  · iframe Hg Lo Hvt Hinv C Hrd
  icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, Lo, Hvt, HA, C, Hrd⟩
  subst hrs
  mcredits (900 * cfg.regularOpCost + ($ep - Ec + X + R))
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Ht
  simp only [res649, hd, htype, Nat.sub_self, List.drop_zero]
  isplitr [HA Hrd S0 S4 S8 Hw]
  · ihave Lo := stk_addr (show (s - 32).toNat - 80 = (s - 32).toNat - 96 + 16 by omega) $$ Lo
    ihave Lo := stk_join n ((s - 32).toNat - 96) 16 80 $$ [Lo16 Lo]
    · iframe Lo16 Lo
    ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
    ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
    · iframe L16 Lo
    ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
    ihave C := stk_intro n _ _ $$ C
    rw [show (bytes32 $c ++ cb.drop 4).length = 12 by simp [bytes32]; omega]
    ihave C := stk_addr (show (s - 32 + 16).toNat = s.toNat - 144 + 112 + 16 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ C
    ihave C := stk_join n (s.toNat - 144 + 112 + 16) 12 4 $$ [C F3]
    · iframe C F3
    ihave F1 := stk_join n (s.toNat - 144 + 112) 16 16 $$ [F0 C]
    · iframe F0 C
    iapply stk_join n (s.toNat - 144) 112 32
    iframe Lo F1
  iexists p, $i
  iframe Hrd S0 S4 S8
  isplitr
  · ipureintro; exact ⟨rfl, hp0, by omega⟩
  subst hL
  iapply sbufE_intro
  iframe HA Hw))

set_option hygiene false in
/-- A simple escape: `push(scratch, v)` (614), then `Ok`. `hd` gives the model's decoding. -/
local macro "push649 " v:term:max : tactic => `(tactic| (
  have hK1 : escK (bs.drop j) = 1 := by simp [escK, hd]
  rw [hK1] at hX hr
  unfold costExt at hX
  generalize hK2 : costApp cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat 1) = K2 at hX
  subst hL
  ihave Hsb := sbuf_join $$ [Hinv Hw]
  · iframe Hinv Hw
  ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
  ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
  · iframe L16 Lo
  have key := ScratchGrow.f614_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) sc $v ptrS capS idx maxP hl live F acc (by omega) (by omega) hcap (by omega) hr
  rw [show UInt32.ofNat 1 = (1 : UInt32) from rfl] at hK2
  rw [hK2] at key
  ihave #S614 := key $$ HG
  rw [show 8 * E - E0 + X + R = K2 + (8 * E - E0 + (X - K2) + R) by omega]
  repeat mstep
  mcall S614 using [Hg Lo Hvt S0 S4 S8 Hsb]
  · iframe Hg Lo Hvt S0 S4 S8 Hsb
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, S0, S4, S8, Hsb⟩
  subst hrs
  mcredits (1700 * cfg.regularOpCost + (8 * E - E0 + (X - K2) + R))
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Ht
  simp only [res649, hd, htype, Nat.sub_self, List.drop_zero, List.length_singleton]
  rw [show MemSet.byteOf $v = ($v : UInt8) from rfl]
  rw [show UInt32.ofNat 1 = (1 : UInt32) from rfl]
  isplitr [Hrd S0 S4 S8 Hsb]
  · ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
    iapply stk_join n (s.toNat - 144) 112 32
    iframe Lo Fr
  iframe Hrd
  iexists p, hl'
  iframe S0 S4 S8 Hsb
  ipureintro; exact hhl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- 649 when the escape is not `\u`. -/
theorem f649_nu (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hr4 : roomFor4 hl maxP 20)
    (hnu : ∀ rest, bs.drop j ≠ 0x75 :: rest)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => cost649 cfg F capS acc bs j)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold escCode at Hk'
  icases Hk' with ⟨#HG, #HE, #H651, #H605, -⟩
  ihave #HE' := HE
  iunfold eofCode at HE'
  icases HE' with ⟨#HErr, -, -, -, #H655, #H653⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #H613, #H614⟩
  ihave #HErr' := HErr
  iunfold errCode at HErr'
  icases HErr' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have ha651 := hm.funcs 651 (by decide)
  have ha614 := hm.funcs 614 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha605 := hm.funcs 605 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hrd, S0, S4, S8, Hsb, Ht⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
  unfold cost649
  generalize hE : costErr cfg F bs.length = E
  generalize hX : costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))) = X
  rw [show 3000 * cfg.regularOpCost + 8 * E + X + R = 3000 * cfg.regularOpCost + (8 * E + X + R) by omega]
  have hE1 := costErr_mono' cfg F j bs.length hj
  icases sbuf_split $$ Hsb with ⟨Hinv, Hw⟩
  generalize hL : (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) = L
  simp only [f649]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  icases stk_split n ((s - 32).toNat - 112) 16 96 $$ Lo with ⟨L16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 112 + 16 = (s - 32).toNat - 96 by omega) $$ Lo
  have key := f655_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    de ptr idx bs j maxP hl L F hde hj (by omega) hptr (by omega) hr4
  generalize hE0 : costErr cfg F j = E0 at key hE1
  rw [hE] at hE1
  ihave #S655 := key $$ HE
  rw [show 8 * E + X + R = E0 + (8 * E - E0 + X + R) by omega]
  mcall S655 using [Hg Lo Hvt Hinv Hrd]
  · iframe Hg Lo Hvt Hinv Hrd
  icases HQ with ⟨Hg, Lo, Hvt, HQ⟩
  by_cases hjl : j < bs.length
  · simp only [res655, dif_pos hjl]
    icases HQ with ⟨%hrs, Hinv, Hrd⟩
    subst hrs
    have hb := okPack_bit de bs[j]
    mcredits (2800 * cfg.regularOpCost + (8 * E - E0 + X + R))
    mstep; mstep; mstep; mstep; mstep
    iterate 11 mstep
    iterate 6 mstep
    rw [okPack_byte]
    obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
    have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
    rw [hx]
    mstep; mstep; mstep
    by_cases hn : x = 110
    · subst hn
      have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((110 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 7 := by
        rw [tab1]; decide
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = some ([10], 1) := by rw [hdrop]; simp [escDecode]
      push649 10
    by_cases hr1 : x = 114
    · subst hr1
      have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((114 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 8 := by
        rw [tab1]; decide
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = some ([13], 1) := by rw [hdrop]; simp [escDecode]
      push649 13
    by_cases ht1 : x = 116
    · subst ht1
      have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((116 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 9 := by
        rw [tab1]; decide
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = some ([9], 1) := by rw [hdrop]; simp [escDecode]
      push649 9
    by_cases hu1 : x = 117
    · exfalso; exact hnu _ (by rw [hdrop, hu1])
    by_cases he1 : x = 111 ∨ x = 112 ∨ x = 113 ∨ x = 115
    · have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[(x.toUInt32 + 4294967186).toNat]?.getD 0 = 1 := by
        rw [tab1, if_neg hn, if_neg hr1, if_neg ht1, if_neg hu1, if_pos he1]
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = none := by
        rw [hdrop]; rcases he1 with h | h | h | h <;> subst h <;> simp [escDecode]
      err649 11 (j + 1) (8 * E - E0)
    · have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[(x.toUInt32 + 4294967186).toNat]?.getD 0 = 0 := by
        rw [tab1, if_neg hn, if_neg hr1, if_neg ht1, if_neg hu1, if_neg he1]
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      mstep; mstep; mstep; mstep
      by_cases hb1 : x = 98
      · subst hb1
        have hk : ([5, 1, 1, 1, 6] : List Nat)[((98 : UInt8).toUInt32 + 4294967198).toNat]?.getD 0 = 5 := by
          rw [tab2]; decide
        iapply FromUtf8Gen.mwpi_br_table_k hk
        isplitr
        · ipureintro; rfl
        clear hk
        mctrl_norm; repeat mpay
        have hd : escDecode (bs.drop j) = some ([8], 1) := by rw [hdrop]; simp [escDecode]
        push649 8
      by_cases hf1 : x = 102
      · subst hf1
        have hk : ([5, 1, 1, 1, 6] : List Nat)[((102 : UInt8).toUInt32 + 4294967198).toNat]?.getD 0 = 6 := by
          rw [tab2]; decide
        iapply FromUtf8Gen.mwpi_br_table_k hk
        isplitr
        · ipureintro; rfl
        clear hk
        mctrl_norm; repeat mpay
        have hd : escDecode (bs.drop j) = some ([12], 1) := by rw [hdrop]; simp [escDecode]
        push649 12
      by_cases he2 : x = 99 ∨ x = 100 ∨ x = 101
      · have hk : ([5, 1, 1, 1, 6] : List Nat)[(x.toUInt32 + 4294967198).toNat]?.getD 0 = 1 := by
          rw [tab2, if_neg hb1, if_neg hf1, if_pos he2]
        iapply FromUtf8Gen.mwpi_br_table_k hk
        isplitr
        · ipureintro; rfl
        clear hk
        mctrl_norm; repeat mpay
        have hd : escDecode (bs.drop j) = none := by
          rw [hdrop]; rcases he2 with h | h | h <;> subst h <;> simp [escDecode]
        err649 11 (j + 1) (8 * E - E0)
      have hk : ([5, 1, 1, 1, 6] : List Nat)[(x.toUInt32 + 4294967198).toNat]?.getD 0 = 0 := by
        rw [tab2, if_neg hb1, if_neg hf1, if_neg he2]
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      by_cases hq : x = 34
      · subst hq
        have h1 : Numeric.bool (Numeric.irelop32 IRelOp.eq (34 : UInt8).toUInt32 34) = 1 := by decide
        repeat mstep
        have hd : escDecode (bs.drop j) = some ([34], 1) := by rw [hdrop]; simp [escDecode]
        push649 34
      have h1 := u8_ne x 34 hq
      by_cases hsl : x = 47
      · subst hsl
        have h2 : Numeric.bool (Numeric.irelop32 IRelOp.eq (47 : UInt8).toUInt32 47) = 1 := by decide
        repeat mstep
        have hd : escDecode (bs.drop j) = some ([47], 1) := by rw [hdrop]; simp [escDecode]
        push649 47
      have h2 := u8_ne x 47 hsl
      by_cases hbs : x = 92
      · subst hbs
        have h3 : Numeric.bool (Numeric.irelop32 IRelOp.eq (92 : UInt8).toUInt32 92) = 1 := by decide
        repeat mstep
        have hd : escDecode (bs.drop j) = some ([92], 1) := by rw [hdrop]; simp [escDecode]
        push649 92
      have h3 := u8_ne x 92 hbs
      repeat mstep
      have hd : escDecode (bs.drop j) = none := by
        rw [hdrop]; simp [escDecode, hq, hsl, hbs, hb1, hf1, hn, hr1, ht1, hu1]
      err649 11 (j + 1) (8 * E - E0)
  · simp only [res655, dif_neg hjl]
    icases HQ with ⟨%p, %⟨hrs, hp0⟩, HA, Hrd⟩
    subst hrs
    have hjeq : j = bs.length := by omega
    mcredits (2800 * cfg.regularOpCost + (8 * E - E0 + X + R))
    have hb := errPack_bit p
    repeat mstep
    rw [errPack_box]
    mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    repeat mstep
    mcredits R
    iframe Hc Hg Hvt Ht
    have hd : escDecode (bs.drop j) = none := by rw [hjeq]; simp [escDecode]
    simp only [res649, hd, htype, Nat.sub_self, List.drop_zero]
    isplitr [HA Hrd S0 S4 S8 Hw]
    · ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
      ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
      · iframe L16 Lo
      ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
      ihave Fr := stk_addr (show s.toNat - 144 + 112 = s.toNat - 144 + 112 by rfl) $$ Fr
      iapply stk_join n (s.toNat - 144) 112 32
      iframe Lo Fr
    iexists p, j
    iframe Hrd S0 S4 S8
    isplitr
    · ipureintro; exact ⟨rfl, hp0, hj⟩
    subst hL
    iapply sbufE_intro
    iframe HA Hw


set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- 649 on `\u` with four hex digits that are not a high surrogate, or no four hex digits. -/
theorem f649_u0 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hr4 : roomFor4 hl maxP 20)
    (hu : ∃ rest, bs.drop j = 0x75 :: rest) (hlo : ∀ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) → nv / 1024 ≠ 54)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => cost649 cfg F capS acc bs j)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold escCode at Hk'
  icases Hk' with ⟨#HG, #HE, #H651, #H605, -⟩
  ihave #HE' := HE
  iunfold eofCode at HE'
  icases HE' with ⟨#HErr, -, -, -, #H655, #H653⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #H613, #H614⟩
  ihave #HErr' := HErr
  iunfold errCode at HErr'
  icases HErr' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have ha651 := hm.funcs 651 (by decide)
  have ha614 := hm.funcs 614 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha605 := hm.funcs 605 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hrd, S0, S4, S8, Hsb, Ht⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
  unfold cost649
  generalize hE : costErr cfg F bs.length = E
  generalize hX : costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))) = X
  rw [show 3000 * cfg.regularOpCost + 8 * E + X + R = 3000 * cfg.regularOpCost + (8 * E + X + R) by omega]
  have hE1 := costErr_mono' cfg F j bs.length hj
  icases sbuf_split $$ Hsb with ⟨Hinv, Hw⟩
  generalize hL : (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) = L
  simp only [f649]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  icases stk_split n ((s - 32).toNat - 112) 16 96 $$ Lo with ⟨L16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 112 + 16 = (s - 32).toNat - 96 by omega) $$ Lo
  have key := f655_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    de ptr idx bs j maxP hl L F hde hj (by omega) hptr (by omega) hr4
  generalize hE0 : costErr cfg F j = E0 at key hE1
  rw [hE] at hE1
  ihave #S655 := key $$ HE
  rw [show 8 * E + X + R = E0 + (8 * E - E0 + X + R) by omega]
  mcall S655 using [Hg Lo Hvt Hinv Hrd]
  · iframe Hg Lo Hvt Hinv Hrd
  icases HQ with ⟨Hg, Lo, Hvt, HQ⟩
  by_cases hjl : j < bs.length
  · simp only [res655, dif_pos hjl]
    icases HQ with ⟨%hrs, Hinv, Hrd⟩
    subst hrs
    have hb := okPack_bit de bs[j]
    mcredits (2800 * cfg.regularOpCost + (8 * E - E0 + X + R))
    mstep; mstep; mstep; mstep; mstep
    iterate 11 mstep
    iterate 6 mstep
    rw [okPack_byte]
    obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
    have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
    rw [hx]
    mstep; mstep; mstep
    have hx117 : x = 117 := by obtain ⟨r, hr⟩ := hu; rw [hdrop] at hr; simp at hr; exact hr.1
    subst hx117
    have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((117 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 10 := by
      rw [tab1]; decide
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have key := f653_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
      de ptr idx bs (j + 1) maxP hl L F hde (by omega) (by omega) hptr (by omega) hr4
    rw [hE] at key
    ihave #S653 := key $$ HE
    rw [show 8 * E - E0 + X + R = E + (7 * E - E0 + X + R) by omega]
    repeat mstep
    mcall S653 using [Hg Lo Hvt Hinv Hrd Ht]
    · iframe Hg Lo Hvt Hinv Hrd Ht
    icases HQ with ⟨Hg, Lo, Hvt, Ht, HQ⟩
    mcredits (2400 * cfg.regularOpCost + (7 * E - E0 + X + R))
    cases hh : hex4 (bs.drop (j + 1)) with
    | none =>
      simp only [SerdeEsc.res653, hh]
      icases HQ with ⟨%p, %jr, %⟨hrs, hp0, hjr⟩, HA, Hrd⟩
      subst hrs
      have hb := errPack_bit16 p
      have hd : escDecode (bs.drop j) = none := by
        rw [hdrop]; simp [escDecode, unicodeEscape, hh]
      boxret649 jr
    | some pr =>
      obtain ⟨nv, r1⟩ := pr
      simp only [SerdeEsc.res653, hh]
      icases HQ with ⟨%hrs, Hinv, Hrd⟩
      subst hrs
      have hh' := hh
      rw [SerdeEsc.hex4_eq] at hh'
      split at hh'
      case isFalse => simp at hh'
      rename_i h4
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hh'
      obtain ⟨nv', hacc4, rfl, rfl⟩ := hh'
      have hnv := SerdeEsc.hexAcc_lt _ _ hacc4
      have h4' : 4 ≤ bs.length - (j + 1) := by simpa using h4
      simp only [List.length_take, List.length_drop, show min 4 (bs.length - (j + 1)) = 4 by omega] at hnv
      have hnv' : nv' < 65536 := by simpa using hnv
      have hb := hexPack_low nv' hnv'
      repeat mstep
      rw [hexPack_val nv' hnv']
      repeat mstep
      rw [mask10 nv' hnv']
      repeat mstep
      rw [eqc _ _ (by omega)]
      by_cases hhi : nv' / 1024 = 54
      · exfalso; exact hlo _ _ hh hhi
      rw [if_neg (by intro h; apply hhi; have : (55296 : UInt32).toNat = 55296 := rfl; omega)]
      repeat mstep
      rw [eqc _ _ (by omega)]
      by_cases hlo : nv' / 1024 = 55
      · rw [if_pos (by rw [hlo]; rfl)]
        have hd : escDecode (bs.drop j) = none := by
          rw [hdrop]; simp [escDecode, ue_lo _ _ _ hh (by omega)]
        err649 17 (j + 1 + 4) (7 * E - E0)
      rw [if_neg (by intro h; apply hlo; have : (56320 : UInt32).toNat = 56320 := rfl; omega)]
      repeat mstep
      rw [mask11 nv' hnv', eqc _ _ (by omega),
        if_neg (by intro h; have : (55296 : UInt32).toNat = 55296 := rfl; omega)]
      repeat mstep
      rw [show UInt32.ofNat nv' &&& 65535 = UInt32.ofNat nv' by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        simp; omega]
      have hcp : nv' < 0x110000 := by omega
      have hd : escDecode (bs.drop j) = some (enc605 nv', (j + 1 + 4) - j) := by
        rw [hdrop]
        simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
          show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
          show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
          show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
        rw [ue_bmp _ _ _ hh (by omega)]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        refine ⟨(enc605_eq _ (by simp [Nat.isValidChar]; omega)).symm, ?_⟩
        simp; omega
      enc649 nv' (j + 1 + 4) (7 * E - E0)
  · exfalso; obtain ⟨r, hr⟩ := hu; have := congrArg List.length hr; simp at this; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- 649 on `\u` with a high surrogate. -/
theorem f649_u1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hr4 : roomFor4 hl maxP 20)
    (hu : ∃ rest, bs.drop j = 0x75 :: rest) (hhi' : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => cost649 cfg F capS acc bs j)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold escCode at Hk'
  icases Hk' with ⟨#HG, #HE, #H651, #H605, -⟩
  ihave #HE' := HE
  iunfold eofCode at HE'
  icases HE' with ⟨#HErr, -, -, -, #H655, #H653⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #H613, #H614⟩
  ihave #HErr' := HErr
  iunfold errCode at HErr'
  icases HErr' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have ha651 := hm.funcs 651 (by decide)
  have ha614 := hm.funcs 614 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha605 := hm.funcs 605 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hrd, S0, S4, S8, Hsb, Ht⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
  unfold cost649
  generalize hE : costErr cfg F bs.length = E
  generalize hX : costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))) = X
  rw [show 3000 * cfg.regularOpCost + 8 * E + X + R = 3000 * cfg.regularOpCost + (8 * E + X + R) by omega]
  have hE1 := costErr_mono' cfg F j bs.length hj
  icases sbuf_split $$ Hsb with ⟨Hinv, Hw⟩
  generalize hL : (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) = L
  simp only [f649]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  icases stk_split n ((s - 32).toNat - 112) 16 96 $$ Lo with ⟨L16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 112 + 16 = (s - 32).toNat - 96 by omega) $$ Lo
  have key := f655_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    de ptr idx bs j maxP hl L F hde hj (by omega) hptr (by omega) hr4
  generalize hE0 : costErr cfg F j = E0 at key hE1
  rw [hE] at hE1
  ihave #S655 := key $$ HE
  rw [show 8 * E + X + R = E0 + (8 * E - E0 + X + R) by omega]
  mcall S655 using [Hg Lo Hvt Hinv Hrd]
  · iframe Hg Lo Hvt Hinv Hrd
  icases HQ with ⟨Hg, Lo, Hvt, HQ⟩
  by_cases hjl : j < bs.length
  · simp only [res655, dif_pos hjl]
    icases HQ with ⟨%hrs, Hinv, Hrd⟩
    subst hrs
    have hb := okPack_bit de bs[j]
    mcredits (2800 * cfg.regularOpCost + (8 * E - E0 + X + R))
    mstep; mstep; mstep; mstep; mstep
    iterate 11 mstep
    iterate 6 mstep
    rw [okPack_byte]
    obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
    have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
    rw [hx]
    mstep; mstep; mstep
    have hx117 : x = 117 := by obtain ⟨r, hr⟩ := hu; rw [hdrop] at hr; simp at hr; exact hr.1
    subst hx117
    have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((117 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 10 := by
      rw [tab1]; decide
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have key := f653_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
      de ptr idx bs (j + 1) maxP hl L F hde (by omega) (by omega) hptr (by omega) hr4
    rw [hE] at key
    ihave #S653 := key $$ HE
    rw [show 8 * E - E0 + X + R = E + (7 * E - E0 + X + R) by omega]
    repeat mstep
    mcall S653 using [Hg Lo Hvt Hinv Hrd Ht]
    · iframe Hg Lo Hvt Hinv Hrd Ht
    icases HQ with ⟨Hg, Lo, Hvt, Ht, HQ⟩
    mcredits (2400 * cfg.regularOpCost + (7 * E - E0 + X + R))
    cases hh : hex4 (bs.drop (j + 1)) with
    | none =>
      exfalso; obtain ⟨nv, r, h, _⟩ := hhi'; rw [hh] at h; simp at h
    | some pr =>
      obtain ⟨nv, r1⟩ := pr
      simp only [SerdeEsc.res653, hh]
      icases HQ with ⟨%hrs, Hinv, Hrd⟩
      subst hrs
      have hh' := hh
      rw [SerdeEsc.hex4_eq] at hh'
      split at hh'
      case isFalse => simp at hh'
      rename_i h4
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hh'
      obtain ⟨nv', hacc4, rfl, rfl⟩ := hh'
      have hnv := SerdeEsc.hexAcc_lt _ _ hacc4
      have h4' : 4 ≤ bs.length - (j + 1) := by simpa using h4
      simp only [List.length_take, List.length_drop, show min 4 (bs.length - (j + 1)) = 4 by omega] at hnv
      have hnv' : nv' < 65536 := by simpa using hnv
      have hb := hexPack_low nv' hnv'
      repeat mstep
      rw [hexPack_val nv' hnv']
      repeat mstep
      rw [mask10 nv' hnv']
      repeat mstep
      rw [eqc _ _ (by omega)]
      by_cases hhi : nv' / 1024 = 54
      · rw [if_pos (by rw [hhi]; rfl)]
        have hnv1 : 0xD800 ≤ nv' ∧ nv' < 0xDC00 := by omega
        have hr1 : List.drop 4 (List.drop (j + 1) bs) = bs.drop (j + 1 + 4) := by simp [List.drop_drop]
        repeat mstep
        have key := f655_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
          de ptr idx bs (j + 1 + 4) maxP hl L F hde (by omega) (by omega) hptr (by omega) hr4
        have hE1 := costErr_mono' cfg F (j + 1 + 4) bs.length (by omega)
        rw [hE] at hE1
        generalize hE1' : costErr cfg F (j + 1 + 4) = E1 at key hE1
        ihave #S655b := key $$ HE
        mcredits (2300 * cfg.regularOpCost + (7 * E - E0 + X + R))
        rw [show 7 * E - E0 + X + R = E1 + (7 * E - E0 - E1 + X + R) by omega]
        mcall S655b using [Hg Lo Hvt Hinv Hrd]
        · iframe Hg Lo Hvt Hinv Hrd
        icases HQ with ⟨Hg, Lo, Hvt, HQ⟩
        mcredits (2000 * cfg.regularOpCost + (7 * E - E0 - E1 + X + R))
        by_cases hj5 : j + 1 + 4 < bs.length
        · simp only [res655, dif_pos hj5]
          icases HQ with ⟨%hrs, Hinv, Hrd⟩
          subst hrs
          obtain ⟨b1, hb1⟩ : ∃ b1, bs[j + 1 + 4] = b1 := ⟨_, rfl⟩
          have hd5 : bs.drop (j + 1 + 4) = b1 :: bs.drop (j + 1 + 4 + 1) := by
            rw [List.drop_eq_getElem_cons hj5, hb1]
          rw [hb1]
          have hb := okPack_bit de b1
          repeat mstep
          rw [okPack_ff00, t5c]
          by_cases h92 : b1 = 92
          · rw [if_pos h92]
            subst h92
            repeat mstep
            have key := f655_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
              de ptr idx bs (j + 1 + 4 + 1) maxP hl L F hde (by omega) (by omega) hptr (by omega) hr4
            have hE2 := costErr_mono' cfg F (j + 1 + 4 + 1) bs.length (by omega)
            rw [hE] at hE2
            generalize hE2' : costErr cfg F (j + 1 + 4 + 1) = E2 at key hE2
            ihave #S655c := key $$ HE
            mcredits (1900 * cfg.regularOpCost + (7 * E - E0 - E1 + X + R))
            rw [show 7 * E - E0 - E1 + X + R = E2 + (7 * E - E0 - E1 - E2 + X + R) by omega]
            mcall S655c using [Hg Lo Hvt Hinv Hrd]
            · iframe Hg Lo Hvt Hinv Hrd
            icases HQ with ⟨Hg, Lo, Hvt, HQ⟩
            mcredits (1700 * cfg.regularOpCost + (7 * E - E0 - E1 - E2 + X + R))
            by_cases hj6 : j + 1 + 4 + 1 < bs.length
            · simp only [res655, dif_pos hj6]
              icases HQ with ⟨%hrs, Hinv, Hrd⟩
              subst hrs
              obtain ⟨b2, hb2⟩ : ∃ b2, bs[j + 1 + 4 + 1] = b2 := ⟨_, rfl⟩
              have hd6 : bs.drop (j + 1 + 4 + 1) = b2 :: bs.drop (j + 1 + 4 + 1 + 1) := by
                rw [List.drop_eq_getElem_cons hj6, hb2]
              rw [hb2]
              have hb := okPack_bit de b2
              repeat mstep
              rw [okPack_ff00, t75]
              by_cases h117 : b2 = 117
              · rw [if_pos h117]
                subst h117
                repeat mstep
                have key := f653_spec (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm (by omega) Cg gt
                  (s - 32) de ptr idx bs (j + 1 + 4 + 1 + 1) maxP hl L F hde (by omega) (by omega) hptr (by omega) hr4
                rw [hE] at key
                ihave #S653b := key $$ HE
                mcredits (1600 * cfg.regularOpCost + (7 * E - E0 - E1 - E2 + X + R))
                rw [show 7 * E - E0 - E1 - E2 + X + R = E + (6 * E - E0 - E1 - E2 + X + R) by omega]
                mcall S653b using [Hg Lo Hvt Hinv Hrd Ht]
                · iframe Hg Lo Hvt Hinv Hrd Ht
                icases HQ with ⟨Hg, Lo, Hvt, Ht, HQ⟩
                mcredits (1200 * cfg.regularOpCost + (6 * E - E0 - E1 - E2 + X + R))
                have hr2 : bs.drop (j + 1 + 4) = 0x5C :: 0x75 :: bs.drop (j + 1 + 4 + 1 + 1) := by rw [hd5, hd6]
                have hue := ue_hi _ _ _ _ hh hnv1 (by rw [hr1, hr2])
                cases hh2 : hex4 (bs.drop (j + 1 + 4 + 1 + 1)) with
                | none =>
                  simp only [SerdeEsc.res653, hh2]
                  icases HQ with ⟨%p, %jr, %⟨hrs, hp0, hjr⟩, HA, Hrd⟩
                  subst hrs
                  have hb := errPack_bit16 p
                  have hd : escDecode (bs.drop j) = none := by
                    rw [hdrop]
                    simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
                      show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
                      show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
                      show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
                    rw [hue, hh2]; rfl
                  boxret649 jr
                | some pr2 =>
                  obtain ⟨mv, r3'⟩ := pr2
                  simp only [SerdeEsc.res653, hh2]
                  icases HQ with ⟨%hrs, Hinv, Hrd⟩
                  subst hrs
                  have hh2' := hh2
                  rw [SerdeEsc.hex4_eq] at hh2'
                  split at hh2'
                  case isFalse => simp at hh2'
                  rename_i h4b
                  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hh2'
                  obtain ⟨mv', hacc4b, rfl, rfl⟩ := hh2'
                  have h4b' : 4 ≤ bs.length - (j + 1 + 4 + 1 + 1) := by simpa using h4b
                  have hmv := SerdeEsc.hexAcc_lt _ _ hacc4b
                  simp only [List.length_take, List.length_drop,
                    show min 4 (bs.length - (j + 1 + 4 + 1 + 1)) = 4 by omega] at hmv
                  have hmv' : mv' < 65536 := by simpa using hmv
                  have hb := hexPack_low mv' hmv'
                  repeat mstep
                  rw [hexPack_val mv' hmv']
                  repeat mstep
                  rw [mask10 mv' hmv', eqc _ _ (by omega)]
                  by_cases hmlo : mv' / 1024 = 55
                  · rw [if_pos (by rw [hmlo]; rfl)]
                    have hmv1 : 0xDC00 ≤ mv' ∧ mv' < 0xE000 := by omega
                    have hcp : (nv' - 55296) * 1024 + (mv' - 56320) + 65536 < 0x110000 := by omega
                    have hd : escDecode (bs.drop j) = some (enc605 ((nv' - 55296) * 1024 + (mv' - 56320) + 65536),
                        (j + 1 + 4 + 1 + 1 + 4) - j) := by
                      rw [hdrop]
                      simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
                        show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
                        show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
                        show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
                      rw [hue, hh2]
                      simp only [Option.bind_some]
                      rw [if_pos hmv1]
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
                      refine ⟨?_, ?_⟩
                      · rw [show 0x10000 + (nv' - 0xD800) * 0x400 + (mv' - 0xDC00) =
                          (nv' - 55296) * 1024 + (mv' - 56320) + 65536 by omega]
                        exact (enc605_eq _ (by simp [Nat.isValidChar]; omega)).symm
                      · simp; omega
                    have hdH : FromUtf8Gen.Hide (escDecode (bs.drop j) = some (enc605 ((nv' - 55296) * 1024 + (mv' - 56320) + 65536),
                        (j + 1 + 4 + 1 + 1 + 4) - j)) := hd
                    clear hue hh hh2 hr2 hacc4 hacc4b hd hcp
                    repeat mstep
                    rw [sub_k nv' 0xD800 4294912000 (by omega) hnv' rfl]
                    repeat mstep
                    rw [ne16 _ (by omega)]
                    repeat mstep
                    rw [sub_k mv' 0xDC00 4294910976 (by omega) hmv' rfl]
                    repeat mstep
                    rw [ne16 _ (by omega)]
                    repeat mstep
                    rw [raw_eq _ _ (by omega) (by omega)]
                    repeat mstep
                    generalize hraw : (nv' - 55296) * 1024 + (mv' - 56320) = raw
                    have hraw1 : raw < 1048576 := by omega
                    have hraw2 : 65536 ≤ raw + 65536 ∧ raw + 65536 < 0x110000 := by omega
                    rw [hraw] at hdH
                    clear hraw hnv1 hmv1 hhi hmlo
                    rw [show UInt32.ofNat raw + 65536 = UInt32.ofNat (raw + 65536) by
                      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp <;> omega]
                    rw [mask27 _ (by omega) (by omega)]
                    iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
                    isplitr; · (ipureintro; exact ⟨rfl, by omega, trivial⟩)
                    inext; iintro Hc; mstep_post
                    rw [if_pos trivial]
                    have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat raw) 1048575) = 0 := by
                      have h1 : (UInt32.ofNat raw).toNat = raw := by rw [UInt32.toNat_ofNat']; omega
                      have h2 : ¬ ((1048575 : UInt32) < UInt32.ofNat raw) := by
                        rw [UInt32.lt_iff_toNat_lt, h1]; show ¬ (1048575 < raw); omega
                      simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, h2, decide_false]
                      rfl
                    mstep
                    mstep
                    mstep
                    rw [hgt]
                    iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
                    isplitr; · (ipureintro; exact ⟨rfl, by omega, trivial⟩)
                    inext; iintro Hc; mstep_post
                    rw [if_pos trivial]
                    have h1 : (UInt32.ofNat (raw + 65536)).toNat = raw + 65536 := by rw [UInt32.toNat_ofNat']; omega
                    generalize hcpv : UInt32.ofNat (raw + 65536) = cpv at h1
                    have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne cpv 1114112) = 1 := by
                      have : cpv ≠ 1114112 := fun e => by
                        rw [e] at h1; have : (1114112 : UInt32).toNat = 1114112 := rfl; omega
                      have h' : (cpv != 1114112) = true := by simp [this]
                      simp only [Numeric.bool, Numeric.irelop32, h', if_true]
                    mstep; mstep; mstep
                    mstep
                    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
                    rw [← hcpv]
                    have hd : escDecode (bs.drop j) = some (enc605 (raw + 65536), (j + 1 + 4 + 1 + 1 + 4) - j) := hdH
                    have hcp : raw + 65536 < 0x110000 := hraw2.2
                    clear hdH h1 hne hcpv
                    repeat mstep
                    enc649 (raw + 65536) (j + 1 + 4 + 1 + 1 + 4) (6 * E - E0 - E1 - E2)
                  · rw [if_neg (by intro h; apply hmlo; have : (56320 : UInt32).toNat = 56320 := rfl; omega)]
                    repeat mstep
                    have hd : escDecode (bs.drop j) = none := by
                      rw [hdrop]
                      simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
                        show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
                        show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
                        show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
                      rw [hue, hh2]
                      simp only [Option.bind_some]
                      rw [if_neg (by omega)]; rfl
                    err649 17 (j + 1 + 4 + 1 + 1 + 4) (6 * E - E0 - E1 - E2)
              · rw [if_neg h117]
                repeat mstep
                have hd : escDecode (bs.drop j) = none := by
                  rw [hdrop]
                  simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
                    show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
                    show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
                    show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
                  rw [ue_hi_nobs _ _ _ hh hnv1 (by rw [hr1, hd5, hd6]; intro r2 h; simp at h; exact h117 h.1)]
                  rfl
                err649 20 (j + 1 + 4 + 1 + 1) (7 * E - E0 - E1 - E2)
            · simp only [res655, dif_neg hj6]
              icases HQ with ⟨%p, %⟨hrs, hp0⟩, HA, Hrd⟩
              subst hrs
              have hb := errPack_bit p
              have hd : escDecode (bs.drop j) = none := by
                rw [hdrop]
                simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
                  show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
                  show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
                  show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
                rw [ue_hi_nobs _ _ _ hh hnv1 (by
                  rw [hr1, hd5, List.drop_eq_nil_of_le (by omega)]; intro r2 h; simp at h)]
                rfl
              boxret649 (j + 1 + 4 + 1)
          · rw [if_neg h92]
            repeat mstep
            have hd : escDecode (bs.drop j) = none := by
              rw [hdrop]
              simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
                show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
                show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
                show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
              rw [ue_hi_nobs _ _ _ hh hnv1 (by rw [hr1, hd5]; intro r2 h; simp at h; exact h92 h.1)]
              rfl
            err649 20 (j + 1 + 4 + 1) (7 * E - E0 - E1)
        · simp only [res655, dif_neg hj5]
          icases HQ with ⟨%p, %⟨hrs, hp0⟩, HA, Hrd⟩
          subst hrs
          have hb := errPack_bit p
          have hd : escDecode (bs.drop j) = none := by
            rw [hdrop]
            simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
              show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
              show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
              show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
            rw [ue_hi_nobs _ _ _ hh hnv1 (by rw [hr1, List.drop_eq_nil_of_le (by omega)]; intro r2 h; simp at h)]
            rfl
          boxret649 (j + 1 + 4)
      exfalso; obtain ⟨nv, r, h, e⟩ := hhi'; rw [hh] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · exfalso; obtain ⟨r, hr⟩ := hu; have := congrArg List.length hr; simp at this; omega

set_option maxRecDepth 100000 in
/-- **`parse_escape(rd, scratch)`** (649) on every input: `res649`, at most `cost649`. -/
theorem f649_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hr4 : roomFor4 hl maxP 20)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => cost649 cfg F capS acc bs j)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  by_cases hu : ∃ rest, bs.drop j = 0x75 :: rest
  · by_cases hh : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54
    · exact f649_u1 cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr sc ptrS capS idx bs acc j maxP hl live F
        hde hj hsc hlen hptr hs hcap hacc hr4 hu hh hr
    · exact f649_u0 cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr sc ptrS capS idx bs acc j maxP hl live F
        hde hj hsc hlen hptr hs hcap hacc hr4 hu (fun nv r h e => hh ⟨nv, r, h, e⟩) hr
  · exact f649_nu cfg lim d type htype inst mi A n g ta hm hd Cg gt s de ptr sc ptrS capS idx bs acc j maxP hl live F
      hde hj hsc hlen hptr hs hcap hacc hr4 (fun rest h => hu ⟨rest, h⟩) hr

end L649

end WNear.Binary.ParseEscape
