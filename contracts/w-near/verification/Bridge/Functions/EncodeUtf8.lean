import Bridge.Functions.SerdeEscRead

/-!
# `char::encode_utf8` (605) (M6)

`parse_escape` (649) writes the decoded code point into a 4-byte buffer on its frame:

```wat
;; 605 encode_utf8(out, c, buf)   c < 0x80: 1 byte; c < 0x800: 2; c ≥ 0x10000: 4; else 3;
;;                                out := (buf, len)
```

* `enc605 c`: the bytes, as Lean's `String.utf8EncodeChar` computes them on `c` (`enc605_eq`: equal
  on a valid code point).
* `f605_spec`: the bytes at `buf`, `(buf, |enc605 c|)` at `out`, for `c < 0x110000`.
-/

namespace WNear.Binary.EncodeUtf8

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.MemSet (byteOf storeBytes_i32_1)

/-- The UTF-8 encoding of the code point `v`, as `String.utf8EncodeChar` computes it. -/
def enc605 (v : Nat) : List UInt8 :=
  if v ≤ 0x7f then [UInt8.ofNat v]
  else if v ≤ 0x7ff then [UInt8.ofNat (v / 64 % 0x20 + 0xc0), UInt8.ofNat (v % 0x40 + 0x80)]
  else if v ≤ 0xffff then
    [UInt8.ofNat (v / 4096 % 0x10 + 0xe0), UInt8.ofNat (v / 64 % 0x40 + 0x80), UInt8.ofNat (v % 0x40 + 0x80)]
  else
    [UInt8.ofNat (v / 262144 % 0x08 + 0xf0), UInt8.ofNat (v / 4096 % 0x40 + 0x80),
      UInt8.ofNat (v / 64 % 0x40 + 0x80), UInt8.ofNat (v % 0x40 + 0x80)]

theorem enc605_eq (v : Nat) (h : v.isValidChar) : enc605 v = String.utf8EncodeChar (Char.ofNat v) := by
  have hv : (Char.ofNat v).val.toNat = v := by
    simp [Char.ofNat, Char.ofNatAux, h]
  unfold String.utf8EncodeChar
  simp only [hv]
  rfl

theorem enc605_length (v : Nat) :
    (enc605 v).length = if v < 128 then 1 else if v < 2048 then 2 else if v < 65536 then 3 else 4 := by
  unfold enc605
  split_ifs <;> simp <;> omega

set_option maxRecDepth 100000 in
theorem lo6 : ∀ r < 64, byteOf (UInt32.ofNat r ||| 128) = UInt8.ofNat (r + 128) := by decide +kernel

set_option maxRecDepth 100000 in
theorem lo5 : ∀ r < 32, byteOf (UInt32.ofNat r ||| 192) = UInt8.ofNat (r + 192) := by decide +kernel

set_option maxRecDepth 100000 in
theorem lo4 : ∀ r < 16, byteOf (UInt32.ofNat r ||| 224) = UInt8.ofNat (r + 224) := by decide +kernel

set_option maxRecDepth 100000 in
theorem lo3 : ∀ r < 8, byteOf (UInt32.ofNat r ||| 240) = UInt8.ofNat (r + 240) := by decide +kernel

theorem and63 (c : UInt32) : c &&& 63 = UInt32.ofNat (c.toNat % 64) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, show (63 : UInt32).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem shr_toNat (c : UInt32) (k : Nat) (hk : k < 32) : (c >>> UInt32.ofNat k).toNat = c.toNat / 2 ^ k := by
  rw [UInt32.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : k < 32)]

theorem shr_eq (c : UInt32) (k : Nat) (hk : k < 32) : c >>> UInt32.ofNat k = UInt32.ofNat (c.toNat / 2 ^ k) := by
  apply UInt32.toNat_inj.mp
  rw [shr_toNat c k hk, UInt32.toNat_ofNat']
  have := c.toNat_lt
  have : c.toNat / 2 ^ k ≤ c.toNat := Nat.div_le_self _ _
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem b63 (c : UInt32) : byteOf (c &&& 63 ||| 128) = UInt8.ofNat (c.toNat % 64 + 128) := by
  rw [and63, lo6 _ (Nat.mod_lt _ (by decide))]

theorem b63s (c : UInt32) (k : Nat) (hk : k < 32) :
    byteOf (c >>> UInt32.ofNat k &&& 63 ||| 128) = UInt8.ofNat (c.toNat / 2 ^ k % 64 + 128) := by
  rw [b63, shr_toNat c k hk]

theorem bhi (c : UInt32) (k m top : Nat) (hk : k < 32) (h : c.toNat / 2 ^ k < m)
    (hl : ∀ r < m, byteOf (UInt32.ofNat r ||| UInt32.ofNat top) = UInt8.ofNat (r + top)) :
    byteOf (c >>> UInt32.ofNat k ||| UInt32.ofNat top) = UInt8.ofNat (c.toNat / 2 ^ k + top) := by
  rw [shr_eq c k hk, hl _ h]

section L605

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem split4 (n a : Nat) (w0 w1 w2 w3 : UInt8) :
    (n ↦[wms][ a ] [w0, w1, w2, w3] : IProp GF) ⊢
      n ↦[wms][ a ] [w0] ∗ n ↦[wms][ a + 1 ] [w1] ∗ n ↦[wms][ a + 2 ] [w2] ∗ n ↦[wms][ a + 3 ] [w3] := by
  iintro H
  icases (MemCpy.memBytes_cons n a w0 [w1, w2, w3]).1 $$ H with ⟨H0, H⟩
  icases (MemCpy.memBytes_cons n (a + 1) w1 [w2, w3]).1 $$ H with ⟨H1, H⟩
  icases (MemCpy.memBytes_cons n (a + 1 + 1) w2 [w3]).1 $$ H with ⟨H2, H3⟩
  rw [show a + 1 + 1 = a + 2 by omega, show a + 2 + 1 = a + 3 by omega]
  iframe H0 H1 H2 H3

theorem join4 (n a : Nat) (w0 w1 w2 w3 : UInt8) :
    n ↦[wms][ a ] [w0] ∗ n ↦[wms][ a + 1 ] [w1] ∗ n ↦[wms][ a + 2 ] [w2] ∗ n ↦[wms][ a + 3 ] [w3] ⊢
      (n ↦[wms][ a ] [w0, w1, w2, w3] : IProp GF) := by
  iintro ⟨H0, H1, H2, H3⟩
  iapply (MemCpy.memBytes_cons n a w0 [w1, w2, w3]).2
  iframe H0
  iapply (MemCpy.memBytes_cons n (a + 1) w1 [w2, w3]).2
  iframe H1
  iapply (MemCpy.memBytes_cons n (a + 1 + 1) w2 [w3]).2
  rw [show a + 1 + 1 = a + 2 by omega, show a + 2 + 1 = a + 3 by omega]
  iframe H2 H3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`char::encode_utf8(out, c, buf)`** (605): `enc605 c` at `buf`, `(buf, len)` at `out`. -/
theorem f605_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out c buf : UInt32) (ob wb : List UInt8)
    (hob : ob.length = 8) (hwb : wb.length = 4) (hc : c.toNat < 0x110000)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hbuf : buf.toNat + 4 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f605 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 c, .i32 buf]⌝ ∗ n ↦[wms][ out.toNat ] ob ∗
          n ↦[wms][ buf.toNat ] wb))
        (fun _ => 60 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] buf ∗
          n ↦[i32][ out.toNat + 4 ] UInt32.ofNat (enc605 c.toNat).length ∗
          n ↦[wms][ buf.toNat ] (enc605 c.toNat ++ wb.drop (enc605 c.toNat).length))) := by
  obtain ⟨w0, w1, w2, w3, rfl⟩ : ∃ w0 w1 w2 w3, wb = [w0, w1, w2, w3] := by
    match wb, hwb with
    | [w0, w1, w2, w3], _ => exact ⟨w0, w1, w2, w3, rfl⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho, Hw⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  icases split4 n buf.toNat w0 w1 w2 w3 $$ Hw with ⟨W0, W1, W2, W3⟩
  simp only [f605]
  by_cases h1 : c.toNat < 128
  · have hl : Numeric.bool (Numeric.irelop32 IRelOp.lt_u c 128) = 1 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, h1]
    repeat mstep
    mstep [W0]
    rw [storeBytes_i32_1]
    repeat mstep
    mstep [O4]
    repeat mstep
    mstep [O0]
    mcredits R
    iframe Hc O0
    have he : enc605 c.toNat = [byteOf c] := by simp [enc605, byteOf, show c.toNat ≤ 127 by omega]
    rw [he]
    simp only [List.length_singleton, List.drop_succ_cons, List.drop_zero, List.singleton_append]
    rw [show UInt32.ofNat 1 = (1 : UInt32) from rfl]
    iframe O4
    iapply join4 n buf.toNat
    iframe W0 W1 W2 W3
  · have hl : Numeric.bool (Numeric.irelop32 IRelOp.lt_u c 128) = 0 := by
      simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
    by_cases h2 : c.toNat < 2048
    · have hl2 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u c 2048) = 1 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, h2]
      repeat mstep
      mstep [W1]
      rw [storeBytes_i32_1]
      repeat mstep
      mstep [W0]
      rw [storeBytes_i32_1]
      repeat mstep
      mstep [O4]
      repeat mstep
      mstep [O0]
      mcredits R
      iframe Hc O0
      have hb0 : byteOf (c >>> (6 % 32) ||| 192) = UInt8.ofNat (c.toNat / 64 % 32 + 0xc0) := by
        rw [show (6 : UInt32) % 32 = UInt32.ofNat 6 from rfl, show (192 : UInt32) = UInt32.ofNat 192 from rfl,
          bhi c 6 32 192 (by decide) (by simp; omega) lo5]
        congr 1; omega
      have hb1 := b63 c
      have he : enc605 c.toNat = [UInt8.ofNat (c.toNat / 64 % 32 + 0xc0), UInt8.ofNat (c.toNat % 64 + 128)] := by
        simp [enc605, show ¬ c.toNat ≤ 127 by omega, show c.toNat ≤ 2047 by omega]
      rw [he]
      simp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append]
      rw [show UInt32.ofNat (0 + 1 + 1) = (2 : UInt32) from rfl]
      iframe O4
      rw [← hb0, ← hb1]
      iapply join4 n buf.toNat
      iframe W0 W1 W2 W3
    · have hl2 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u c 2048) = 0 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
      have hb63 := b63 c
      have hb6 : byteOf (c >>> (6 % 32) &&& 63 ||| 128) = UInt8.ofNat (c.toNat / 64 % 64 + 128) := by
        rw [show (6 : UInt32) % 32 = UInt32.ofNat 6 from rfl, b63s c 6 (by decide)]; rfl
      by_cases h3 : c.toNat < 65536
      · have hl3 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u c 65536) = 0 := by
          simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le]; omega
        repeat mstep
        mstep [W2]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [W0]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [W1]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [O4]
        repeat mstep
        mstep [O0]
        mcredits R
        iframe Hc O0
        have hb0 : byteOf (c >>> (12 % 32) ||| 224) = UInt8.ofNat (c.toNat / 4096 % 16 + 0xe0) := by
          rw [show (12 : UInt32) % 32 = UInt32.ofNat 12 from rfl, show (224 : UInt32) = UInt32.ofNat 224 from rfl,
            bhi c 12 16 224 (by decide) (by simp; omega) lo4]
          congr 1; omega
        have he : enc605 c.toNat = [UInt8.ofNat (c.toNat / 4096 % 16 + 0xe0), UInt8.ofNat (c.toNat / 64 % 64 + 128),
            UInt8.ofNat (c.toNat % 64 + 128)] := by
          simp [enc605, show ¬ c.toNat ≤ 127 by omega, show ¬ c.toNat ≤ 2047 by omega, show c.toNat ≤ 65535 by omega]
        rw [he]
        simp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append]
        rw [show UInt32.ofNat (0 + 1 + 1 + 1) = (3 : UInt32) from rfl]
        iframe O4
        rw [← hb0, ← hb6, ← hb63]
        iapply join4 n buf.toNat
        iframe W0 W1 W2 W3
      · have hl3 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u c 65536) = 1 := by
          simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le]; omega
        repeat mstep
        mstep [W3]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [W0]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [W2]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [W1]
        rw [storeBytes_i32_1]
        repeat mstep
        mstep [O4]
        repeat mstep
        mstep [O0]
        mcredits R
        iframe Hc O0
        have hb0 : byteOf (c >>> (18 % 32) ||| 240) = UInt8.ofNat (c.toNat / 262144 % 8 + 0xf0) := by
          rw [show (18 : UInt32) % 32 = UInt32.ofNat 18 from rfl, show (240 : UInt32) = UInt32.ofNat 240 from rfl,
            bhi c 18 8 240 (by decide) (by simp; omega) lo3]
          congr 1; omega
        have hb12 : byteOf (c >>> (12 % 32) &&& 63 ||| 128) = UInt8.ofNat (c.toNat / 4096 % 64 + 128) := by
          rw [show (12 : UInt32) % 32 = UInt32.ofNat 12 from rfl, b63s c 12 (by decide)]; rfl
        have he : enc605 c.toNat = [UInt8.ofNat (c.toNat / 262144 % 8 + 0xf0), UInt8.ofNat (c.toNat / 4096 % 64 + 128),
            UInt8.ofNat (c.toNat / 64 % 64 + 128), UInt8.ofNat (c.toNat % 64 + 128)] := by
          simp [enc605, show ¬ c.toNat ≤ 127 by omega, show ¬ c.toNat ≤ 2047 by omega, show ¬ c.toNat ≤ 65535 by omega]
        rw [he]
        simp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append]
        rw [show UInt32.ofNat (0 + 1 + 1 + 1 + 1) = (4 : UInt32) from rfl]
        iframe O4
        rw [← hb0, ← hb12, ← hb6, ← hb63]
        iapply join4 n buf.toNat
        iframe W0 W1 W2 W3

end L605

end WNear.Binary.EncodeUtf8
