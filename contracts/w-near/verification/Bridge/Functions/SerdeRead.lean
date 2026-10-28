import Bridge.Functions.ArgsLeaves
import Bridge.Functions.MemCpy
import Bridge.Functions.BorrowMut
import NearInterface.Json

/-!
# serde_json's reader over a slice (M6): peek, eat, whitespace

The JSON deserializer (`Deserializer<SliceRead>`, `ArgsLeaves.deserializer`) begins with
its `SliceRead`, `(ptr, len, index)`: the input `bs` at `ptr`, `len = bs.length`, and the
position `i ≤ len`. Every function here sees it through that triple (`sliceRead`), the
input owned beside it, and returns `Result<Option<u8>, Error>` packed in an `i64`: bit 0
the `Err` tag (never set on a slice), bit 8 `Some`, the byte at bits 16..23 (`optByte`).

```wat
;; 332 peek(de) -> i64            index < len ? (bs[index] << 16) | 256 : 0
;; 324 next_char(de) -> i64       the same, and index += 1 when some
;; 637 SliceRead::next(rd) -> i64 the same as 324, on the read itself
;; 333 eat_char(de)               index += 1 (checked: panics on overflow, never here)
;; 329 peek_or_null(de) -> i64    peek, then Ok(byte or 0) at bits 8..15
;; 339 parse_whitespace(de) -> i64
loop
  peek(de)  None → Ok(None)
  b ∉ " \t\n\r" (bit (b - 9) of 0x800013) → Ok(Some b)
  eat_char(de)
```

* `optByte`, `wsLen` (the leading whitespace of a byte list, as `NearInterface.Json`'s
  `isWhitespace` counts it) and its link to `skipWhitespace`.
* `f332_spec` (peek, 24), `f333_spec` (eat_char, 12), `f324_spec` (next_char, 31), `f637_spec`
  (next, 31), `f329_spec` (peek_or_null, 65: `byteOrNull`).
* `f339_spec` (parse_whitespace, `100 + 96 w`): from `i`, past the `w = wsLen (bs.drop i)`
  whitespace bytes, to the first other byte (or the end): `optByte (bs[i + w]?)`, index `i + w`.
  The loop (`inv339`) is proved once; the byte tests are `decide`d over all 256 bytes
  (`ws_range`, `ws_bit`, `nws_cases`), the byte kept abstract in the steps (`generalize`)
  so that `mstep` never evaluates it.

Costs are in `regular_op_cost`s, activation excluded, and bound every outcome.
-/

namespace WNear.Binary.SerdeRead

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.ArgsLeaves (sliceRead)

/-- `Option<u8>` as the reader returns it, `Ok` (bit 0 clear): `Some` at bit 8, the byte at
bits 16..23. -/
def optByte : Option UInt8 → UInt64
  | none => 0
  | some b => b.toUInt64 <<< 16 ||| 256

section Peek

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The reader's state: the `SliceRead` at `de` over `bs` at `ptr`, at index `i`. -/
def rd (n : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat) : IProp GF :=
  iprop(sliceRead n de ptr (UInt32.ofNat bs.length) (UInt32.ofNat i) ∗ n ↦[wms][ ptr.toNat ] bs)

/-- **`peek`** (332): the byte at the index, if any. -/
theorem f332_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f332 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => 24 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (optByte bs[i]?)]⌝ ∗ rd n de ptr bs i)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hrd⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨R0, R4, R8⟩, Hbs⟩
  simp only [f332]
  repeat mstep
  mstep [R8]
  mstep; mstep; mstep [R4]
  by_cases hil : i < bs.length
  · have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hil
    ihave Hbs := MemCpy.memBytes_pick n ptr.toNat i bs hil $$ Hbs
    icases Hbs with ⟨B1, Bk, B2⟩
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat bs.length)) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    repeat mstep
    mstep [R0]
    repeat mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    repeat mstep
    iframe Hc
    isplitr
    · ipureintro
      simp [htype, optByte, hb, Memory.decodeLE]
    iunfold rd, sliceRead
    ihave Hbs := MemCpy.memBytes_unpick n ptr.toNat i (bs.take i) bs[i] (bs.drop (i + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    have es : List.take i bs ++ bs[i] :: List.drop (i + 1) bs = bs := by simp
    rw [es]
    iframe R0 R4 R8 Hbs
  · have hc : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat bs.length)) = 1 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    isplitr
    · ipureintro
      simp [htype, optByte, List.getElem?_eq_none (Nat.le_of_not_lt hil)]
    iunfold rd, sliceRead
    iframe R0 R4 R8 Hbs

theorem ofNat_succ (i : Nat) (h : i + 1 < 2 ^ 32) : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
  apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add] <;> omega

/-- **`eat_char`** (333): the index one further (its overflow check never fails: `i < len`). -/
theorem f333_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i < bs.length) (hlen : bs.length < 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f333 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => 12 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ rd n de ptr bs (i + 1))) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hrd⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨R0, R4, R8⟩, Hbs⟩
  have hc : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i + 1) (UInt32.ofNat i)) = 1 := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le, UInt32.toNat_add]; omega
  simp only [f333]
  repeat mstep
  mstep [R8]
  repeat mstep
  mstep [R8]
  repeat mstep
  rw [ofNat_succ i (by omega)]
  iframe Hc
  iunfold rd, sliceRead
  iframe R0 R4 R8 Hbs

/-- **`next_char`** (324): the byte at the index, if any, and the index past it. -/
theorem f324_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f324 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => 31 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (optByte bs[i]?)]⌝ ∗ rd n de ptr bs (min (i + 1) bs.length))) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hrd⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨R0, R4, R8⟩, Hbs⟩
  simp only [f324]
  repeat mstep
  mstep [R8]
  mstep; mstep; mstep [R4]
  by_cases hil : i < bs.length
  · have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hil
    ihave Hbs := MemCpy.memBytes_pick n ptr.toNat i bs hil $$ Hbs
    icases Hbs with ⟨B1, Bk, B2⟩
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat bs.length)) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    repeat mstep
    mstep [R0]
    repeat mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    repeat mstep
    mstep [R8]
    repeat mstep
    iframe Hc
    isplitr
    · ipureintro
      simp [htype, optByte, hb, Memory.decodeLE]
    rw [show min (i + 1) bs.length = i + 1 by omega, ofNat_succ i (by omega)]
    iunfold rd, sliceRead
    ihave Hbs := MemCpy.memBytes_unpick n ptr.toNat i (bs.take i) bs[i] (bs.drop (i + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    have es : List.take i bs ++ bs[i] :: List.drop (i + 1) bs = bs := by simp
    rw [es]
    iframe R0 R4 R8 Hbs
  · have hc : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat bs.length)) = 1 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    have hm : min (i + 1) bs.length = i := by omega
    rw [hm]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    isplitr
    · ipureintro
      simp [htype, optByte, List.getElem?_eq_none (Nat.le_of_not_lt hil)]
    iunfold rd, sliceRead
    iframe R0 R4 R8 Hbs

/-- `SliceRead::next` (637) has `next_char`'s body. -/
theorem f637_eq : f637 = f324 := rfl

/-- **`SliceRead::next`** (637), on the read itself: as `next_char` (324). -/
theorem f637_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f637 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => 31 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (optByte bs[i]?)]⌝ ∗ rd n de ptr bs (min (i + 1) bs.length))) := by
  rw [f637_eq]
  exact f324_spec cfg lim d type htype inst mi n hn Cg de ptr bs i hi hlen hptr hde

theorem uint8_forall {P : UInt8 → Prop} (h : ∀ k, k < 256 → P (UInt8.ofNat k)) : ∀ b, P b := by
  intro b
  have := h b.toNat b.toNat_lt
  simpa using this

theorem optByte_ok (o : Option UInt8) : (optByte o &&& 1 == 0) = true := by
  cases o with
  | none => rfl
  | some b => revert b; exact uint8_forall (by decide +kernel)

theorem optByte_some (b : UInt8) :
    Numeric.bool (Numeric.bool (optByte (some b) &&& 256 == 0) == 0) = 1 := by
  revert b; exact uint8_forall (by decide +kernel)

theorem optByte_byte (b : UInt8) : (optByte (some b) >>> (16 % 64)).toUInt32 &&& 255 = b.toUInt32 := by
  revert b; exact uint8_forall (by decide +kernel)

/-- A whitespace byte passes 339.s range check `b - 9 ≤ 23`. -/
theorem ws_range (b : UInt8) (h : NearInterface.Json.isWhitespace b = true) :
    Numeric.bool (Numeric.irelop32 IRelOp.gt_u (b.toUInt32 + 4294967287) 23) = 0 := by
  revert b h; exact uint8_forall (by decide +kernel)

/-- A whitespace byte has its bit in 339.s mask `0x800013` (bits 0, 1, 4, 23: `\t \n \r ' '`). -/
theorem ws_bit (b : UInt8) (h : NearInterface.Json.isWhitespace b = true) :
    Numeric.bool ((1 : UInt32) <<< ((b.toUInt32 + 4294967287) % 32) &&& 8388627 == 0) = 0 := by
  revert b h; exact uint8_forall (by decide +kernel)

/-- A byte that is not whitespace fails 339.s range check or its mask. -/
theorem nws_cases (b : UInt8) (h : NearInterface.Json.isWhitespace b = false) :
    Numeric.bool (Numeric.irelop32 IRelOp.gt_u (b.toUInt32 + 4294967287) 23) = 1 ∨
      (Numeric.bool (Numeric.irelop32 IRelOp.gt_u (b.toUInt32 + 4294967287) 23) = 0 ∧
        Numeric.bool ((1 : UInt32) <<< ((b.toUInt32 + 4294967287) % 32) &&& 8388627 == 0) = 1) := by
  revert b h; exact uint8_forall (by decide +kernel)

/-- 339.s result on `Some b`: the byte and the `Some` bit kept. -/
theorem optByte_keep (b : UInt8) :
    (optByte (some b) &&& 256 ||| optByte (some b) &&& 18446744069431296000 ||| 0) = optByte (some b) := by
  revert b; exact uint8_forall (by decide +kernel)

/-- `peek_or_null`'s value: the byte at the index, or 0, at bits 8..15 (`Ok`). -/
def byteOrNull (o : Option UInt8) : UInt64 := (o.getD 0).toUInt64 <<< 8

theorem byteOrNull_eq (o : Option UInt8) :
    (optByte o >>> 8 &&& Numeric.intToUInt64 ((optByte o <<< 55).toIntS >>> (63 : Nat)) &&& 65280 |||
      optByte o &&& 18446744069414584320) = byteOrNull o := by
  cases o with
  | none => decide +kernel
  | some b => revert b; exact uint8_forall (by decide +kernel)

/-- **`peek_or_null`** (329): the byte at the index, or 0. -/
theorem f329_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a332 : Nat) (ha332 : mi.funcAddrs[332]? = some a332)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) :
    a332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f329 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => 65 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (byteOrNull bs[i]?)]⌝ ∗ rd n de ptr bs i)) := by
  iintro ⟨#F332, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hrd⟩
  subst hargs
  have t11 : types[11]!.params.length = 1 := by rfl
  simp only [f329]
  repeat mstep
  mcall (f332_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn Cg de ptr bs i hi hlen hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok : Numeric.bool (optByte bs[i]? &&& 1 == 0) = 1 := by simp only [optByte_ok]; rfl
  repeat mstep
  iframe Hc Hrd
  ipureintro
  simp [htype, byteOrNull_eq]

end Peek

/-! ## Whitespace -/

open NearInterface.Json (isWhitespace skipWhitespace)

/-- The number of whitespace bytes `bs` starts with. -/
def wsLen : List UInt8 → Nat
  | [] => 0
  | b :: bs => if isWhitespace b then wsLen bs + 1 else 0

theorem wsLen_le (bs : List UInt8) : wsLen bs ≤ bs.length := by
  induction bs with
  | nil => simp [wsLen]
  | cons b bs ih => simp only [wsLen]; split <;> simp; omega

/-- The bytes before `wsLen` are whitespace. -/
theorem wsLen_ws (bs : List UInt8) (k : Nat) (hk : k < wsLen bs) :
    ∃ b, bs[k]? = some b ∧ isWhitespace b = true := by
  induction bs generalizing k with
  | nil => simp [wsLen] at hk
  | cons b bs ih =>
    simp only [wsLen] at hk
    split at hk
    · rcases k with _ | k
      · exact ⟨b, rfl, by assumption⟩
      · simpa using ih k (by omega)
    · omega

/-- The byte at `wsLen`, if any, is not whitespace. -/
theorem wsLen_stop (bs : List UInt8) (b : UInt8) (h : bs[wsLen bs]? = some b) :
    isWhitespace b = false := by
  induction bs with
  | nil => simp at h
  | cons c bs ih =>
    simp only [wsLen] at h
    split at h
    · exact ih (by simpa using h)
    · simp at h; subst h; simpa using (by assumption : ¬ isWhitespace c = true)

theorem skipWhitespace_eq (bs : List UInt8) : skipWhitespace bs = bs.drop (wsLen bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [skipWhitespace, wsLen, List.dropWhile_cons] at ih ⊢
    split <;> simp_all

end WNear.Binary.SerdeRead

namespace WNear.Binary.SerdeRead

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.ArgsLeaves (sliceRead)

section Ws

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 339's frame: the deserializer and its four locals. -/
def fr339 (inst : Nat) (mi : ModuleInst) (de : UInt32) (l1 l2 l3 : UInt64) (l4 : UInt32) : Frame :=
  ⟨#[.i32 de, .i64 l1, .i64 l2, .i64 l3, .i32 l4], inst, mi⟩

/-- `parse_whitespace`'s loop invariant: `k` of the `w` whitespace bytes eaten, credits for
the `w - k` iterations left (`W` each) and the exit (`E`). -/
def inv339 (n inst : Nat) (mi : ModuleInst) (Cg c₀ W E R : Nat) (de ptr : UInt32) (bs : List UInt8)
    (i w : Nat) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l1 l2 l3 : UInt64) (l4 : UInt32), ⌜X = [] ∧ g = fr339 inst mi de l1 l2 l3 l4 ∧ k ≤ w⌝ ∗
    credits Cg (W * (w - k) * c₀ + E * c₀ + R) ∗ rd n de ptr bs (i + k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`parse_whitespace`** (339): past the whitespace from `i` (`wsLen (bs.drop i)` bytes) to
the next byte, which it returns (`Ok(Some b)`), or to the end (`Ok(None)`). -/
theorem f339_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a332 a333 : Nat) (ha332 : mi.funcAddrs[332]? = some a332)
    (ha333 : mi.funcAddrs[333]? = some a333)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) :
    a332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗ a333 ↪[wf] FuncInst.wasm types[0]! inst f333 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f339 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => (100 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (optByte bs[i + wsLen (bs.drop i)]?)]⌝ ∗
          rd n de ptr bs (i + wsLen (bs.drop i)))) := by
  iintro ⟨#F332, #F333, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hrd⟩
  subst hargs
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  generalize hw : wsLen (bs.drop i) = w
  have hwl : i + w ≤ bs.length := by have := wsLen_le (bs.drop i); simp at this; omega
  simp only [f339]
  repeat mstep
  rw [show (100 + 96 * w) * cfg.regularOpCost + R = cfg.regularOpCost + (96 * (w - 0) * cfg.regularOpCost + 99 * cfg.regularOpCost + R) by
    rw [Nat.sub_zero, Nat.add_mul]; omega]
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 96 * (w - 0) * cfg.regularOpCost + 99 * cfg.regularOpCost + R)
    (I := inv339 n inst mi Cg cfg.regularOpCost 96 99 R de ptr bs i w) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv339 at HI
    icases HI with ⟨%k, %l1, %l2, %l3, %l4, %⟨hX, hg, hk⟩, Hc, Hrd⟩
    subst hX
    have hik : i + k ≤ bs.length := by omega
    have hok : Numeric.bool (optByte bs[i + k]? &&& 1 == 0) = 1 := by simp only [optByte_ok]; rfl
    by_cases hkw : k < w
    · obtain ⟨b, hb, hws⟩ := wsLen_ws (bs.drop i) k (by omega)
      rw [List.getElem?_drop] at hb
      rw [hb] at hok
      rw [show 96 * (w - k) * cfg.regularOpCost + 99 * cfg.regularOpCost + R =
        96 * cfg.regularOpCost + (96 * (w - (k + 1)) * cfg.regularOpCost + 99 * cfg.regularOpCost + R) by
          rw [show 96 * (w - k) = 96 + 96 * (w - (k + 1)) by omega, Nat.add_mul]; omega]
      generalize hZ : 96 * (w - (k + 1)) * cfg.regularOpCost = Z
      rw [hg]
      simp only [fr339]
      repeat mstep
      mcall (f332_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn Cg de ptr bs (i + k) hik hlen hptr hde) using [Hrd]
      · iframe Hrd
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      rw [hb]
      have hsome := optByte_some b
      generalize hv : optByte (some b) = v at hok hsome ⊢
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep
      mstep_taken with simp [hsome]
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      have hbyte : (v >>> (16 % 64)).toUInt32 &&& 255 = b.toUInt32 := by rw [← hv]; exact optByte_byte b
      have hr := ws_range b hws
      clear hv
      rw [hbyte]
      generalize hx : b.toUInt32 + 4294967287 = x at hr ⊢
      have hbit := ws_bit b hws
      rw [hx] at hbit
      mstep_not_taken with exact hr
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with exact hbit
      have hi1 : i + k < bs.length := by
        rcases Nat.lt_or_ge (i + k) bs.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hb; simp at hb
      mstep
      mcall (f333_spec cfg (lim := lim) (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (i + k) hi1 hlen hde) using [Hrd]
      · iframe Hrd
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      mstep
      simp only [Post.mloop, List.reverse_nil]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iunfold inv339
      iexists k + 1
      iexists v
      iexists 0
      iexists v &&& 256
      iexists x
      rw [Nat.add_assoc]
      iframe Hrd
      isplitr
      · ipureintro; exact ⟨rfl, rfl, by omega⟩
      rw [← hZ]
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    · have hkw' : k = w := by omega
      subst hkw'
      rw [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
      rw [hg]
      simp only [fr339]
      repeat mstep
      mcall (f332_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn Cg de ptr bs (i + k) hik hlen hptr hde) using [Hrd]
      · iframe Hrd
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      rcases hbk : bs[i + k]? with _ | b
      · rw [hbk] at hok
        simp only [optByte] at hok ⊢
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep; mstep; mstep
        simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero]
        mpay
        repeat mstep
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        iframe Hrd
        ipureintro
        simp [htype]
      · have hstop := wsLen_stop (bs.drop i) b (by rw [hw, List.getElem?_drop]; exact hbk)
        rw [hbk] at hok
        have hsome := optByte_some b
        generalize hv : optByte (some b) = v at hok hsome ⊢
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep
        mstep_taken with simp [hsome]
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        have hbyte : (v >>> (16 % 64)).toUInt32 &&& 255 = b.toUInt32 := by rw [← hv]; exact optByte_byte b
        have hkeep := optByte_keep b
        rw [hv] at hkeep
        clear hv
        rw [hbyte]
        have hcases := nws_cases b hstop
        generalize hx : b.toUInt32 + 4294967287 = x at hcases ⊢
        rcases hcases with hr | ⟨hr, hbit⟩
        · mstep_taken with exact hr
          simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero]
          mpay
          repeat mstep
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iframe Hrd
          ipureintro
          rw [hkeep]; simp [htype]
        · mstep_not_taken with exact hr
          mstep; mstep; mstep; mstep; mstep; mstep
          mstep_taken with exact hbit
          simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero]
          mpay
          repeat mstep
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iframe Hrd
          ipureintro
          rw [hkeep]; simp [htype]
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  iunfold inv339
  iexists 0
  iexists 0
  iexists 0
  iexists 0
  iexists 0
  simp only [Nat.add_zero]
  iframe Hc Hrd
  ipureintro
  simp [fr339]

end Ws

end WNear.Binary.SerdeRead
