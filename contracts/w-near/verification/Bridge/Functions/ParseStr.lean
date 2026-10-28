import Bridge.Functions.FromUtf8

/-!
# serde_json's `SliceRead::parse_str` (646), the plain case (M6)

A JSON string's body, after its opening `"`, read into `Reference<str>`:

```wat
;; 583 <Range as SliceIndex>::index(out, a, b, ptr, len, loc)   out := (ptr + a, b - a) (a ≤ b ≤ len)
;; 648 as_str(out, rd, p, len)        927(sp, p, len); Err → 657 (InvalidUnicodeCodePoint)
;;                                    Ok → out := (0, p, len)
;; 646 parse_str(out, rd, scratch)    a 48-byte frame
loop                                  ;; once per escape
  start := index
  while index < len and ESCAPE[[ptr + index]] = 0: index += 1     ;; the scan, the table at 1062392
  index = len → Err(EofWhileParsingString) (647)
  b = '\' → scratch += [start, index); index += 1; parse_escape (649); loop
  b ≠ '"' → index += 1; Err(ControlCharacterWhileParsingString) (647)
  b = '"', scratch empty     → (s, n) := 583(start, index); index += 1; as_str(s, n)
                               → out := (0, Borrowed, s, n)
  b = '"', scratch not empty → scratch += [start, index); index += 1; as_str(scratch)
                               → out := (0, Copied, p, n)
```

* `escTable` (`escData_segment`: the data segment's bytes), `plain`, `esc_at`: the table is `0`
  exactly on the bytes `parse_str` scans past.
* `f583_spec` (20), `f648_spec_ascii` (`cost648 len = 40 + cost927 len`, on ASCII bytes).
* `f646_spec_plain`: from `i`, a body of plain ASCII bytes up to a `"`, the scratch empty:
  `Ok(Reference::Borrowed(ptr + i, body.length))` at `out`, the reader at `i + body.length + 1`, at
  `200 + 30 · body.length + cost648 body.length`, an 80-byte stack. The outer loop is entered once
  (its back edge follows an escape), so its invariant is the state at entry; the scan loop's
  (`invS`) holds `30` per byte left.
* `plain_model`: on the same input, `NearInterface.Json.stringBody` decodes the string whose bytes
  are `body`, with the same rest (`stringBody_plain`, `fromUTF8_ascii`).

Not yet: the escapes (649, 653, 605, the scratch appends 613/614, and 728), non-ASCII bytes (927's
general validator), and the reject paths (647/657, which allocate the error box).
-/

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word pair64 storeBytes_pair64 load_pair64)
open WNear.Binary.FromUtf8 (res927 cost927)

section L583

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`<Range<usize> as SliceIndex<[u8]>>::index(out, a, b, ptr, len, loc)`** (583) for
`a ≤ b ≤ len`: the subslice `(ptr + a, b - a)` (its two panics not reached). -/
theorem f583_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out a b ptr len loc : UInt32) (ob : List UInt8)
    (hob : ob.length = 8) (_hout : out.toNat + 8 ≤ 2 ^ 32) (hab : a.toNat ≤ b.toNat) (hbl : b.toNat ≤ len.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f583 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 a, .i32 b, .i32 ptr, .i32 len, .i32 loc]⌝ ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 20 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] (ptr + a) ∗ n ↦[i32][ out.toNat + 4 ] (b - a))) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  have h1 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u b a) = 0 := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
  have h2 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u len b) = 0 := by
    simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
  simp only [f583]
  repeat mstep
  mstep [O4]
  mstep; mstep; mstep; mstep
  mstep [O0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe O0 O4

end L583

end WNear.Binary.ParseStr

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word pair64 storeBytes_pair64 load_pair64)
open WNear.Binary.FromUtf8 (res927 cost927)

section L648

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `as_str`'s cost: 927's, its activation and 648's own. -/
def cost648 (len : Nat) : Nat := 40 + cost927 len

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::as_str(out, rd, p, len)`** (648) on ASCII `bs` at `p`: `Ok(&str)`, `(0, p, len)` at
`out`, through `from_utf8` (927) in a 32-byte frame. -/
theorem f648_spec_ascii (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a927 : Nat)
    (ha927 : mi.funcAddrs[927]? = some a927) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd p len : UInt32) (ob bs : List UInt8) (hob : ob.length = 12)
    (_hout : out.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = len.toNat) (hp : p.toNat + len.toNat ≤ 2 ^ 32)
    (hsp : 32 ≤ sp.toNat) (hA : ∀ b ∈ bs, b.toNat < 128) :
    a927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f648 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd, .i32 p, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ p.toNat ] bs))
        (fun _ => cost648 len.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 32) 32 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] len ∗
          n ↦[wms][ p.toNat ] bs)) := by
  iintro ⟨#F927, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hb⟩
  subst hargs
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 32) 12 20 $$ Hs with ⟨Hs12, Hs20⟩
  iunfold stk at Hs12
  icases Hs12 with ⟨%sb, %hsb, Hs12⟩
  simp only [f648, cost648]
  rw [show (40 + cost927 len.toNat) * cfg.regularOpCost + R = 40 * cfg.regularOpCost + (cost927 len.toNat * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  generalize hK : cost927 len.toNat * cfg.regularOpCost = K
  have hK2 : (16 + cost927 len.toNat) * cfg.regularOpCost = 16 * cfg.regularOpCost + K := by rw [Nat.add_mul, hK]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  ihave Hs12 := AllocNewCell.memBytes_addr (show sp.toNat - 32 = (sp - 32).toNat by omega) $$ Hs12
  mcall (FromUtf8.f927_spec_ascii cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 32) p len sb bs
    hsb (by omega) hbs hp hA) using [Hs12 Hb]
  · iframe Hs12 Hb
  rw [hK2, show 32 * cfg.regularOpCost + (K + R) - (16 * cfg.regularOpCost + K) = 16 * cfg.regularOpCost + R by omega]
  icases HQ with ⟨%hrs, Hb, Hres⟩
  subst hrs
  iunfold res927 at Hres
  rw [if_pos (Utf8.utf8Ok_of_ascii bs hA)]
  icases Hres with ⟨R0, R4, R8⟩
  ihave R48 := KeyGet.join64 n ((sp - 32).toNat + 4) p len $$ [R4 R8]
  · rw [show (sp - 32).toNat + 4 + 4 = (sp - 32).toNat + 8 by omega]; iframe R4 R8
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O48⟩
  mstep; mstep; mstep
  mstep [R0]
  mstep; mstep; mstep
  mstep; mstep
  mstep [R48]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [O48]
  rw [storeBytes_pair64]
  mstep; mstep
  mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  ihave O48 := KeyGet.split64 n (out.toNat + 4) p len $$ O48
  icases O48 with ⟨O4, O8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe Hg O0 O4 O8 Hb
  ihave R04 := stk_word n (sp - 32).toNat 0 $$ R0
  ihave R48 := stk_intro n ((sp - 32).toNat + 4) _ $$ R48
  ihave R12 := stk_join n (sp - 32).toNat 4 8 $$ [R04 R48]
  · simp only [List.length_append, bytes32_length]; iframe R04 R48
  rw [h32]
  iapply stk_join n (sp.toNat - 32) 12 20
  iframe R12 Hs20

end L648

end WNear.Binary.ParseStr

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)

set_option hygiene false in
/-- A `br_if` taken (the condition `h`), out of the enclosing blocks. -/
local macro "brt " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, $h⟩
  mctrl_norm; repeat mpay))

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

/-- serde_json's `ESCAPE` table at 1062392: nonzero exactly at the control bytes, `"` and `\`. -/
def escTable : List UInt8 :=
  (List.range 256).map fun k => if k < 0x20 || k == 0x22 || k == 0x5C then 1 else 0

set_option maxRecDepth 100000 in
/-- The table is the data segment's bytes at 1062392. -/
theorem escData_segment :
    (List.range 256).map (fun k => wNearSource.read (159306 + (1062392 - 1048576) + k)) = escTable := by
  decide +kernel

theorem escTable_length : escTable.length = 256 := by simp [escTable]

/-- A byte `parse_str` scans past: not a control byte, `"` or `\`. -/
def plain (b : UInt8) : Bool := 0x20 ≤ b.toNat && b.toNat != 0x22 && b.toNat != 0x5C

set_option maxRecDepth 100000 in
theorem esc_at (b : UInt8) :
    (escTable[b.toNat]'(by rw [escTable_length]; exact b.toNat_lt)).toUInt32 = if plain b then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

section L646

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 646's frame: `(out, rd, scratch, sp, len, start, end, ptr, index, byte)`. -/
def fr646 (inst : Nat) (mi : ModuleInst) (out de sc sp l4 l5 l6 l7 l8 l9 : UInt32) : Frame :=
  ⟨#[.i32 out, .i32 de, .i32 sc, .i32 sp, .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i32 l8, .i32 l9], inst, mi⟩

/-- The scan loop's invariant: at `k ≤ i + m` (the index stored too), `30` per byte left. -/
def invS (n inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (out de sc sp l4 l5 l6 l7 : UInt32) (i m : Nat)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l9 : UInt32), ⌜X = [] ∧ g = fr646 inst mi out de sc sp l4 l5 l6 l7 (UInt32.ofNat k) l9 ∧
      i ≤ k ∧ k ≤ i + m⌝ ∗
    credits Cg (30 * (i + m - k) * c₀ + E * c₀ + R) ∗ n ↦[i32][ de.toNat + 8 ] UInt32.ofNat k ∗ P)

theorem invS_intro (n inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (out de sc sp l4 l5 l6 l7 : UInt32)
    (i m : Nat) (P : IProp GF) (k : Nat) (l9 : UInt32) (h1 : i ≤ k) (h2 : k ≤ i + m) :
    credits Cg (30 * (i + m - k) * c₀ + E * c₀ + R) ∗ n ↦[i32][ de.toNat + 8 ] UInt32.ofNat k ∗ P ⊢
      invS n inst mi Cg c₀ E R out de sc sp l4 l5 l6 l7 i m P []
        ⟨#[.i32 out, .i32 de, .i32 sc, .i32 sp, .i32 l4, .i32 l5, .i32 l6, .i32 l7, .i32 (UInt32.ofNat k), .i32 l9],
          inst, mi⟩ := by
  iintro ⟨Hc, D8, HP⟩
  iunfold invS
  iexists k
  iexists l9
  iframe Hc D8 HP
  ipureintro; exact ⟨rfl, rfl, h1, h2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::parse_str(out, rd, scratch)`** (646), the plain case: from `i`, ASCII bytes with no
escape up to a `"`, the scratch empty: `Ok(Reference::Borrowed(ptr + i, body.length))`, the reader past the
`"`. -/
theorem f646_spec_plain (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 a648 a927 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (ha648 : mi.funcAddrs[648]? = some a648)
    (ha927 : mi.funcAddrs[927]? = some a927) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr : UInt32) (ob bs body rest : List UInt8) (i : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (_hde : de.toNat + 12 ≤ 2 ^ 32) (_hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 80 ≤ sp.toNat) (hsplit : bs.drop i = body ++ 0x22 :: rest)
    (hplain : ∀ b ∈ body, plain b = true ∧ b.toNat < 128) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ a648 ↪[wf] FuncInst.wasm types[45]! inst f648 ∗
      a927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable))
        (fun _ => (200 + 30 * body.length + cost648 body.length) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 80) 80 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] 0 ∗
          n ↦[i32][ out.toNat + 8 ] (ptr + UInt32.ofNat i) ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat body.length) ∗
          rd n de ptr bs (i + body.length + 1) ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable)) := by
  iintro ⟨#F583, #F648, #F927, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hrd, Hsc, He⟩
  subst hargs
  have hil : i + body.length + 1 ≤ bs.length := by
    have := congrArg List.length hsplit; simp at this; omega
  have hlt := sp.toNat_lt
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  simp only [f646]
  rw [show (200 + 30 * body.length + cost648 body.length) * cfg.regularOpCost + R =
    60 * cfg.regularOpCost + ((140 + 30 * body.length) * cfg.regularOpCost + (cost648 body.length * cfg.regularOpCost + R)) by
      simp only [Nat.add_mul]; omega]
  generalize hK : cost648 body.length * cfg.regularOpCost = K
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  generalize hW : (140 + 30 * body.length) * cfg.regularOpCost = W
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 54 * cfg.regularOpCost + (W + (K + R)))
    (I := fun X fr => iprop(⌜X = [] ∧ fr = fr646 inst mi out de sc (sp - 48) 0 0 0 0 0 0⌝ ∗
      credits Cg (54 * cfg.regularOpCost + (W + (K + R))) ∗ stk n (sp.toNat - 80) 80 ∗
      n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗
      n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
      n ↦[i32][ de.toNat + 8 ] UInt32.ofNat i ∗ n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%⟨hX, hfr⟩, Hc, Hs, Ho, Hsc, He, D0, D4, D8, Hb, Hg⟩
    subst hX
    rw [hfr]
    simp only [fr646]
    clear hfr
    mstep; mstep [D4]; mstep; mstep; mstep [D8]
    mstep; mstep; mstep; mstep
    have hil' : i < bs.length := by omega
    have hsel : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat i)) ≠ 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
    iapply mwpi_cons
    iapply FromUtf8.mwpi_select'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; omega
    inext
    iintro Hc
    rw [if_neg hsel]
    clear hsel
    mctrl_norm
    mstep; mstep; mstep [D0]; mstep; mstep; mstep
    mstep; mstep
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 30 * (i + body.length - i) * cfg.regularOpCost + 160 * cfg.regularOpCost + (K + R))
      (I := invS n inst mi Cg cfg.regularOpCost 160 (K + R) out de sc (sp - 48) (UInt32.ofNat bs.length) (UInt32.ofNat i)
        (UInt32.ofNat bs.length) ptr i body.length
        iprop(stk n (sp.toNat - 80) 80 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
          n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold invS at HI
      icases HI with ⟨%k, %l9, %⟨hX, hfr, hik, hkm⟩, Hc, D8, HP⟩
      subst hX
      rw [hfr]
      simp only [fr646]
      clear hfr
      icases HP with ⟨Hs, Ho, Hsc, He, D0, D4, Hb, Hg⟩
      have hkl : k < bs.length := by omega
      have hne : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat bs.length) (UInt32.ofNat k)) = 0 := by
        have hu : (UInt32.ofNat k).toNat = k := by simp; omega
        have hv : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
        generalize UInt32.ofNat k = u at hu ⊢
        generalize UInt32.ofNat bs.length = v at hv ⊢
        have : v ≠ u := fun e => by subst e; omega
        simp [Numeric.bool, Numeric.irelop32, this]
      have hbk : bs[k]? = (body ++ 0x22 :: rest)[k - i]? := by
        rw [← hsplit, List.getElem?_drop]; congr 1; omega
      ihave Hb := MemCpy.memBytes_pick n ptr.toNat k bs hkl $$ Hb
      icases Hb with ⟨B1, Bk, B2⟩
      obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
      rw [hxk]
      rw [List.getElem?_eq_getElem hkl, hxk] at hbk
      have es : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
      by_cases hkm' : k < i + body.length
      · have hxb : plain x = true ∧ x.toNat < 128 := by
          rw [List.getElem?_append_left (by omega)] at hbk
          exact hplain x (List.mem_of_getElem? hbk.symm)
        rw [show 30 * (i + body.length - k) * cfg.regularOpCost + 160 * cfg.regularOpCost + (K + R) =
          190 * cfg.regularOpCost + (30 * (i + body.length - (k + 1)) * cfg.regularOpCost + (K + R)) by
            rw [show i + body.length - k = (i + body.length - (k + 1)) + 1 by omega]; simp only [Nat.mul_add, Nat.add_mul]; omega]
        generalize hZ : 30 * (i + body.length - (k + 1)) * cfg.regularOpCost = Z
        mstep; mstep; mstep
        brn hne
        clear hne
        mstep; mstep; mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.load8]
        ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
        · iframe B1 Bk B2
        rw [es]
        mstep; mstep; mstep
        ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
        icases He with ⟨E1, Ek, E2⟩
        mstep [Ek] with (simp [UInt32.toNat_add]; omega)
        rw [SerdeKey.load8, esc_at, if_pos hxb.1]
        ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
        · iframe E1 Ek E2
        rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
        brn rfl
        mstep; mstep; mstep; mstep; mstep
        mstep [D8]
        rw [SerdeRead.ofNat_succ k (by omega)]
        mstep
        simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iapply invS_intro n inst mi Cg cfg.regularOpCost 160 (K + R) out de sc (sp - 48) _ _ _ ptr i body.length _ (k + 1) _
          (by omega) (by omega)
        iframe D8 Hs Ho Hsc He D0 D4 Hb Hg
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      · have hk : k = i + body.length := by omega
        have hx : x = 0x22 := by
          rw [List.getElem?_append_right (by omega), show k - i - body.length = 0 by omega] at hbk
          simpa using hbk
        have hx256 : x.toNat < 256 := x.toNat_lt
        rw [show 30 * (i + body.length - k) * cfg.regularOpCost = 0 by rw [show i + body.length - k = 0 by omega]; simp,
          Nat.zero_add]
        mstep; mstep; mstep
        brn hne
        clear hne
        mstep; mstep; mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.load8]
        ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
        · iframe B1 Bk B2
        rw [es]
        mstep; mstep; mstep
        ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
        icases He with ⟨E1, Ek, E2⟩
        mstep [Ek] with (simp [UInt32.toNat_add]; omega)
        rw [SerdeKey.load8, esc_at, if_neg (by rw [hx]; decide)]
        ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
        · iframe E1 Ek E2
        rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
        iapply mwpi_cons
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, by decide⟩
        mctrl_norm
        simp only [Post.mloop]
        mctrl_norm
        repeat mpay
        rw [hx]
        have h48 : (sp - 48).toNat = sp.toNat - 48 := by
          rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
        icases stk_split n (sp.toNat - 80) 32 48 $$ Hs with ⟨S32, S48⟩
        rw [show sp.toNat - 80 + 32 = (sp - 48).toNat by omega]
        icases stk_split n (sp - 48).toNat 8 40 $$ S48 with ⟨S8, S40⟩
        icases stk_split n ((sp - 48).toNat + 8) 24 16 $$ S40 with ⟨S24, S16⟩
        icases stk_split n ((sp - 48).toNat + 8 + 24) 12 4 $$ S16 with ⟨S12, S4⟩
        iunfold stk at S8 S12
        icases S8 with ⟨%s8, %hs8, S8⟩
        icases S12 with ⟨%s12, %hs12, S12⟩
        mstep; mstep; mstep; mstep
        brn (by decide)
        mstep; mstep; mstep
        brn (by decide)
        mstep; mstep
        mstep [Hsc]
        brn rfl
        mstep; mstep; mstep; mstep; mstep; mstep
        have t36 : types[36]!.params.length = 6 := by rfl
        mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48) (UInt32.ofNat i)
          (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062248 s8 hs8 (by omega)
          (by simp; omega) (by simp; omega)) using [S8]
        · iframe S8
        icases HQ with ⟨%hrs, P0, P4⟩
        subst hrs
        mstep; mstep; mstep
        mstep [D8]
        mstep; mstep; mstep; mstep; mstep; mstep
        rw [SerdeRead.ofNat_succ k (by omega)]
        have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (k + 1)) (UInt32.ofNat k)) = 0 := by
          rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
        brn hov
        clear hov
        mstep; mstep [P4]; mstep; mstep; mstep [P0]; mstep
        mstep; mstep
        mstep [D8]
        rw [show UInt32.ofNat k - UInt32.ofNat i = UInt32.ofNat body.length by
          apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
        mstep; mstep; mstep; mstep; mstep; mstep
        ihave Hb := U128From.memBytes_split n ptr.toNat i bs (by omega) $$ Hb
        icases Hb with ⟨B0, Bd⟩
        rw [hsplit]
        ihave Bd := U128From.memBytes_split n (ptr.toNat + i) body.length (body ++ 0x22 :: rest) (by simp) $$ Bd
        icases Bd with ⟨Bbody, Brest⟩
        rw [List.take_left' rfl, List.drop_left' rfl]
        ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + i = (ptr + UInt32.ofNat i).toNat by
          simp [UInt32.toNat_add]; omega) $$ Bbody
        ihave S12 := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
          rw [UInt32.toNat_add, h48]; simp; omega) $$ S12
        ihave S32 := VecFromElem.stk_addr (show sp.toNat - 80 = (sp - 48).toNat - 32 by omega) $$ S32
        have t45 : types[45]!.params.length = 4 := by rfl
        have hK3 : (12 + cost648 (UInt32.ofNat body.length).toNat) * cfg.regularOpCost = 12 * cfg.regularOpCost + K := by
          rw [show (UInt32.ofNat body.length).toNat = body.length by simp; omega, Nat.add_mul, hK]
        mcall (f648_spec_ascii cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg a927 ha927 (by omega) Cg gt
          (sp - 48) (sp - 48 + 32) de (ptr + UInt32.ofNat i) (UInt32.ofNat body.length) s12 body hs12
          (by rw [UInt32.toNat_add, h48]; simp; omega) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
          (by omega) (fun b hb => (hplain b hb).2)) using [Hg S32 S12 Bbody]
        · iframe Hg S32 S12 Bbody
        rw [hK3, show 72 * cfg.regularOpCost + (K + R) - (12 * cfg.regularOpCost + K) = 60 * cfg.regularOpCost + R by omega]
        icases HQ with ⟨%hrs, Hg, S32, Q0, Q4, Q8, Bbody⟩
        subst hrs
        have h32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
        rw [h32]
        icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
        icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, Ho⟩
        icases U128From.memBytes_split n (out.toNat + 4 + 4) 4 ((ob.drop 4).drop 4) (by simp; omega) $$ Ho with ⟨O8, O12⟩
        mstep; mstep [Q4]; mstep
        mstep; mstep; mstep [Q0]; mstep; mstep
        brn (by decide)
        mstep; mstep; mstep; mstep
        mstep [O8] with (simp [UInt32.toNat_add]; omega)
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        mstep [Q8] with (simp [UInt32.toNat_add]; omega)
        mstep [O12] with (simp [UInt32.toNat_add]; omega)
        mstep; mstep; mstep; mstep
        mstep; mstep
        mstep [O0]
        mstep; mstep
        mstep [O4]
        mstep
        (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
        mstep; mstep; mstep; mstep [Hg]
        rw [show sp - 48 + 48 = sp by simp]
        repeat mstep
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        isplitr
        · ipureintro; trivial
        iframe Hg Hsc He
        rw [show out.toNat + 4 + 4 + 4 = out.toNat + 12 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
        iframe O0 O4 O8 O12
        isplitr [D0 D4 D8 B0 Bbody Brest]
        · ihave P0 := stk_word n (sp - 48).toNat _ $$ P0
          ihave P4 := stk_word n ((sp - 48).toNat + 4) _ $$ P4
          ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
          ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
          ihave Q8 := stk_word n ((sp - 48).toNat + 32 + 8) _ $$ Q8
          ihave P8 := stk_join n (sp - 48).toNat 4 4 $$ [P0 P4]
          · iframe P0 P4
          ihave Q48 := stk_join n ((sp - 48).toNat + 32 + 4) 4 4 $$ [Q4 Q8]
          · rw [show (sp - 48).toNat + 32 + 4 + 4 = (sp - 48).toNat + 32 + 8 by omega]; iframe Q4 Q8
          ihave Q12 := stk_join n ((sp - 48).toNat + 32) 4 8 $$ [Q0 Q48]
          · iframe Q0 Q48
          ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [P8 S24]
          · iframe P8 S24
          ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
          · iframe S32' Q12
          ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 S4]
          · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 S4
          ihave S80 := stk_join n ((sp - 48).toNat - 32) 32 48 $$ [S32 S48]
          · rw [show (sp - 48).toNat - 32 + 32 = (sp - 48).toNat by omega]; iframe S32 S48
          iapply VecFromElem.stk_addr (show (sp - 48).toNat - 32 = sp.toNat - 80 by omega)
          iexact S80
        iunfold rd, sliceRead
        rw [show i + body.length + 1 = k + 1 by omega]
        iframe D0 D4 D8
        ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat i).toNat = ptr.toNat + i by
          simp [UInt32.toNat_add]; omega) $$ Bbody
        ihave Bd := U128From.memBytes_join n (ptr.toNat + i) body.length body (34 :: rest) rfl $$ [Bbody Brest]
        · iframe Bbody Brest
        rw [← hsplit]
        ihave Bb := U128From.memBytes_join n ptr.toNat i (bs.take i) (bs.drop i) (by simp; omega) $$ [B0 Bd]
        · iframe B0 Bd
        rw [List.take_append_drop]
        iexact Bb
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; rw [← hW]; simp only [Nat.add_mul, Nat.add_sub_cancel_left]; omega
    inext
    iintro Hc
    iapply invS_intro n inst mi Cg cfg.regularOpCost 160 (K + R) out de sc (sp - 48) _ _ _ ptr i body.length _ i _
      le_rfl (by omega)
    iframe Hc D8 Hs Ho Hsc He D0 D4 Hb Hg
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iframe Hc Hs Ho Hsc He D0 D4 D8 Hb Hg
  ipureintro; exact ⟨rfl, rfl⟩

end L646

end WNear.Binary.ParseStr

/-! ## The model side: `stringBody` on a plain body -/

namespace WNear.Binary.ParseStr

open NearInterface.Json (stringBody)

/-- `stringBody` on plain bytes up to a `"`: the bytes, decoded as UTF-8, and the rest. -/
theorem stringBody_plain (body rest acc : List UInt8) (h : ∀ b ∈ body, plain b = true) :
    stringBody (body ++ 0x22 :: rest) acc = some (String.fromUTF8? ⟨(acc.reverse ++ body).toArray⟩, rest) := by
  induction body generalizing acc with
  | nil => simp [stringBody]
  | cons b body ih =>
    have hb := h b (by simp)
    simp only [plain, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hb22 : b ≠ 0x22 := fun e => h2 (by subst e; rfl)
    have hb5c : b ≠ 0x5C := fun e => h3 (by subst e; rfl)
    have hlt : ¬ b < 0x20 := by intro e; have := UInt8.lt_iff_toNat_lt.mp e; simp at this; omega
    rw [List.cons_append, stringBody.eq_13 _ _ _ hb22 (fun _ _ e _ => hb5c e), if_neg hlt,
      ih (b :: acc) (fun x hx => h x (by simp [hx]))]
    simp

theorem mk_toArray (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray := by
  apply ByteArray.ext; simp

/-- ASCII bytes are valid UTF-8, their own encoding. -/
theorem fromUTF8_ascii (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) :
    ∃ s : String, String.fromUTF8? ⟨bs.toArray⟩ = some s ∧ s.toByteArray = ⟨bs.toArray⟩ := by
  have hv : ByteArray.IsValidUTF8 ⟨bs.toArray⟩ := by
    refine ⟨bs.map (fun b => Char.ofNat b.toNat), ?_⟩
    have : (bs.map (fun b => Char.ofNat b.toNat)).flatMap String.utf8EncodeChar = bs := by
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        have hb := h b (by simp)
        simp only [List.map_cons, List.flatMap_cons]
        rw [ih (fun x hx => h x (by simp [hx]))]
        have hc : (Char.ofNat b.toNat).val.toNat = b.toNat := by
          simp [Char.ofNat, Char.ofNatAux, Nat.isValidChar]; split <;> simp_all <;> omega
        rw [String.utf8EncodeChar_eq_singleton]
        · rw [List.singleton_append]
          congr 1
          apply UInt8.toNat_inj.mp
          rw [UInt32.toNat_toUInt8, hc]; omega
        · rw [Char.utf8Size_eq_one_iff]; rw [UInt32.le_iff_toNat_le, hc]; simp; omega
    rw [mk_toArray]
    simp only [List.utf8Encode, this]
  exact ⟨String.fromUTF8 _ hv, by simp only [String.fromUTF8?, dif_pos hv], rfl⟩

/-- **The plain case against the model**: `stringBody` from `i` decodes the string whose bytes are
`body` (the slice `f646_spec_plain` returns) and leaves `rest` (the reader past the `"`). -/
theorem plain_model (bs body rest : List UInt8) (i : Nat) (hsplit : bs.drop i = body ++ 0x22 :: rest)
    (hplain : ∀ b ∈ body, plain b = true ∧ b.toNat < 128) :
    ∃ s : String, stringBody (bs.drop i) [] = some (some s, rest) ∧ s.toByteArray = body.toByteArray := by
  obtain ⟨s, hs, hb⟩ := fromUTF8_ascii body (fun b hb => (hplain b hb).2)
  refine ⟨s, ?_, by rw [hb, mk_toArray]⟩
  rw [hsplit, stringBody_plain body rest [] (fun b hb => (hplain b hb).1)]
  simp [hs]

end WNear.Binary.ParseStr
