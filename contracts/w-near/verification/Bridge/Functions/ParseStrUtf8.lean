import Bridge.Functions.ParseStr
import Bridge.Functions.FromUtf8Gen

/-!
# `parse_str` (646) and `as_str` (648) on UTF-8 bodies (M6)

`ParseStr` proved the borrowed case of `parse_str` on ASCII bodies through `f927_spec_ascii`. With
the general `FromUtf8Gen.f927_spec`, the same proofs carry any body that is valid UTF-8 (the width
table at 1071704 is threaded beside the `ESCAPE` table):

* `f648_spec_valid`: `as_str` on `bs` with `utf8Ok bs`: `Ok(&str)`, at `cost648 len`.
* `f646_spec_utf8`: from `i`, a body of plain bytes (no control byte, `"` or `\`) with
  `utf8Ok body`, then `"`, the scratch empty: `Ok(Reference::Borrowed(ptr + i, body.length))`, the
  reader past the `"`, at `200 + 30 · body.length + cost648 body.length`.
* `utf8_model`: on the same input, `stringBody` decodes the string whose bytes are `body`, and
  leaves the same rest; `utf8_model_bad`: when `body` is not valid UTF-8, `stringBody` gives
  `none` for the string (the binary's `as_str` then fails: 657, an error box, not proved yet).
-/

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word pair64 storeBytes_pair64 load_pair64)
open WNear.Binary.FromUtf8 (res927 cost927)
open WNear.Binary.FromUtf8Gen (utf8Width)
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

section L646

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::as_str(out, rd, p, len)`** (648) on valid UTF-8 `bs` (`utf8Ok`) at `p`: `Ok(&str)`, `(0, p, len)` at
`out`, through `from_utf8` (927) in a 32-byte frame. -/
theorem f648_spec_valid (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a927 : Nat)
    (ha927 : mi.funcAddrs[927]? = some a927) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd p len : UInt32) (ob bs : List UInt8) (hob : ob.length = 12)
    (_hout : out.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = len.toNat) (hp : p.toNat + len.toNat ≤ 2 ^ 32)
    (hsp : 32 ≤ sp.toNat) (hok : Utf8.utf8Ok bs = true) :
    a927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f648 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd, .i32 p, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ p.toNat ] bs ∗
          n ↦[wms][ 1071704 ] utf8Width))
        (fun _ => cost648 len.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 32) 32 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] len ∗
          n ↦[wms][ p.toNat ] bs ∗ n ↦[wms][ 1071704 ] utf8Width)) := by
  iintro ⟨#F927, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hb, Ht⟩
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
  mcall (FromUtf8Gen.f927_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 32) p len sb bs
    hsb (by omega) hbs hp) using [Hs12 Hb Ht]
  · iframe Hs12 Hb Ht
  rw [hK2, show 32 * cfg.regularOpCost + (K + R) - (16 * cfg.regularOpCost + K) = 16 * cfg.regularOpCost + R by omega]
  icases HQ with ⟨%hrs, Hb, Hres, Ht⟩
  subst hrs
  iunfold res927 at Hres
  rw [if_pos hok]
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
  iframe Hg O0 O4 O8 Hb Ht
  ihave R04 := stk_word n (sp - 32).toNat 0 $$ R0
  ihave R48 := stk_intro n ((sp - 32).toNat + 4) _ $$ R48
  ihave R12 := stk_join n (sp - 32).toNat 4 8 $$ [R04 R48]
  · simp only [List.length_append, bytes32_length]; iframe R04 R48
  rw [h32]
  iapply stk_join n (sp.toNat - 32) 12 20
  iframe R12 Hs20


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::parse_str(out, rd, scratch)`** (646), the plain case: from `i`, ASCII bytes with no
escape up to a `"`, the scratch empty: `Ok(Reference::Borrowed(ptr + i, body.length))`, the reader past the
`"`. -/
theorem f646_spec_utf8 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 a648 a927 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (ha648 : mi.funcAddrs[648]? = some a648)
    (ha927 : mi.funcAddrs[927]? = some a927) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr : UInt32) (ob bs body rest : List UInt8) (i : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (_hde : de.toNat + 12 ≤ 2 ^ 32) (_hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 80 ≤ sp.toNat) (hsplit : bs.drop i = body ++ 0x22 :: rest)
    (hplain : ∀ b ∈ body, plain b = true) (hutf : Utf8.utf8Ok body = true) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ a648 ↪[wf] FuncInst.wasm types[45]! inst f648 ∗
      a927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width))
        (fun _ => (200 + 30 * body.length + cost648 body.length) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 80) 80 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] 0 ∗
          n ↦[i32][ out.toNat + 8 ] (ptr + UInt32.ofNat i) ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat body.length) ∗
          rd n de ptr bs (i + body.length + 1) ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width)) := by
  iintro ⟨#F583, #F648, #F927, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hrd, Hsc, He, Hw⟩
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
      n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
      n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
      n ↦[i32][ de.toNat + 8 ] UInt32.ofNat i ∗ n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%⟨hX, hfr⟩, Hc, Hs, Ho, Hsc, He, Hw, D0, D4, D8, Hb, Hg⟩
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
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
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
      icases HP with ⟨Hs, Ho, Hsc, He, Hw, D0, D4, Hb, Hg⟩
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
      · have hxb : plain x = true := by
          rw [List.getElem?_append_left (by omega)] at hbk
          exact hplain x (List.mem_of_getElem? hbk.symm)
        have hx256 := x.toNat_lt
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
        rw [SerdeKey.load8, esc_at, if_pos hxb]
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
        iframe D8 Hs Ho Hsc He Hw D0 D4 Hb Hg
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
        mcall (f648_spec_valid cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg a927 ha927 (by omega) Cg gt
          (sp - 48) (sp - 48 + 32) de (ptr + UInt32.ofNat i) (UInt32.ofNat body.length) s12 body hs12
          (by rw [UInt32.toNat_add, h48]; simp; omega) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
          (by omega) hutf) using [Hg S32 S12 Bbody Hw]
        · iframe Hg S32 S12 Bbody Hw
        rw [hK3, show 72 * cfg.regularOpCost + (K + R) - (12 * cfg.regularOpCost + K) = 60 * cfg.regularOpCost + R by omega]
        icases HQ with ⟨%hrs, Hg, S32, Q0, Q4, Q8, Bbody, Hw⟩
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
        iframe Hg Hsc He Hw
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
    iframe Hc D8 Hs Ho Hsc He Hw D0 D4 Hb Hg
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iframe Hc Hs Ho Hsc He Hw D0 D4 D8 Hb Hg
  ipureintro; exact ⟨rfl, rfl⟩


end L646

/-! ## The model side -/

open NearInterface.Json (stringBody)

/-- **A UTF-8 body against the model**: `stringBody` from `i` decodes the string whose bytes are
`body` (the slice `f646_spec_utf8` returns) and leaves `rest`. -/
theorem utf8_model (bs body rest : List UInt8) (i : Nat) (hsplit : bs.drop i = body ++ 0x22 :: rest)
    (hplain : ∀ b ∈ body, plain b = true) (hutf : Utf8.utf8Ok body = true) :
    ∃ s : String, stringBody (bs.drop i) [] = some (some s, rest) ∧ s.toByteArray = body.toByteArray := by
  have hv : ByteArray.IsValidUTF8 ⟨body.toArray⟩ := (Utf8.utf8Ok_iff_isValidUTF8 body).mp hutf
  refine ⟨String.fromUTF8 _ hv, ?_, by rw [← mk_toArray]; rfl⟩
  rw [hsplit, stringBody_plain body rest [] hplain]
  simp [String.fromUTF8?, hv]

/-- A body that is not UTF-8: the model decodes no string (`stringBody`'s first component `none`). -/
theorem utf8_model_bad (bs body rest : List UInt8) (i : Nat) (hsplit : bs.drop i = body ++ 0x22 :: rest)
    (hplain : ∀ b ∈ body, plain b = true) (hbad : Utf8.utf8Ok body = false) :
    stringBody (bs.drop i) [] = some (none, rest) := by
  rw [hsplit, stringBody_plain body rest [] hplain]
  have h := Utf8.fromUTF8?_isSome body
  rw [hbad] at h
  simp only [List.reverse_nil, List.nil_append]
  rw [Option.isSome_eq_false_iff.mp h |> Option.isNone_iff_eq_none.mp]

end WNear.Binary.ParseStr
