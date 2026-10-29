import Bridge.Functions.ParseStrUtf8
import Bridge.Functions.SerdeErrBox

/-!
# `parse_str` (646) on any escape-free input: the reject paths (M6)

`ParseStrUtf8.f646_spec_utf8` proved the borrowed result on a valid UTF-8 body. This file proves
646 on every input whose scan does not stop at a `\`: from the reader's index `i`, the input is
`body ++ tail`, `body` the plain bytes the scan skips, and `tail` empty or starting with a byte that
stops the scan and is not `\`. Four outcomes:

* `tail = []`: EOF, `Err(EofWhileParsingString)` (code 4) through 647, at the index `i + |body|`;
* `tail = x :: _`, `x` a control byte: the index moves past it, then
  `Err(ControlCharacterWhileParsingString)` (code 15) through 647;
* `tail = '"' :: _`, `utf8Ok body`: `Ok(Reference::Borrowed(ptr + i, |body|))`;
* `tail = '"' :: _`, not `utf8Ok body`: `Err(InvalidUnicodeCodePoint)` through 648 → 657.

`res646` is the postcondition by cases, `cost646` the cost: `300 + 30 · |body| + cost927 |body|`,
plus `costErr cfg F (i + |body| + 1)` on a reject (linear in the index, and the allocator's
`cost310W` on a free list of length `F`).

* `f646_spec_noesc`: the specification.
* `noesc_model`: the model side. `stringBody` from `i` is `none` on the two scan rejects, `some (none,
  rest)` on a bad body, and `some (some s, rest)` with `s`'s bytes `body` on the accepted one.
-/

namespace WNear.Binary.ParseStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.FromUtf8 (res927 cost927)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4 f647_spec f648_spec_bad f657_eq)

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

/-- The accepted case: the scan stops at `"` and the body is UTF-8. -/
def ok646 (body tail : List UInt8) : Prop := tail.head? = some 0x22 ∧ Utf8.utf8Ok body = true

instance (body tail : List UInt8) : Decidable (ok646 body tail) := by unfold ok646; infer_instance

/-- 646's cost on an escape-free input. -/
def cost646 (cfg : WasmConfig) (F i : Nat) (body tail : List UInt8) : Nat :=
  (330 + 30 * body.length + cost927 body.length) * cfg.regularOpCost +
    if ok646 body tail then 0 else costErr cfg F (i + body.length + 1)

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 646's result on an escape-free input: `Ok(Borrowed)` (the heap unchanged), or `Err(box)` (the
reader at the EOF, or past the stopping byte). -/
def res646 (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat) (out de ptr : UInt32)
    (ob bs body tail : List UInt8) (i : Nat) : IProp GF :=
  if ok646 body tail then
    iprop(heapInv n maxP mlen live F ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] 0 ∗
      n ↦[i32][ out.toNat + 8 ] (ptr + UInt32.ofNat i) ∗
      n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat body.length) ∗ rd n de ptr bs (i + body.length + 1))
  else
    iprop(∃ p : UInt32, ⌜p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗ n ↦[i32][ out.toNat ] 1 ∗
      n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[wms][ out.toNat + 8 ] (ob.drop 8) ∗
      rd n de ptr bs (i + body.length + if tail = [] then 0 else 1))

end Defs

set_option maxRecDepth 100000 in
theorem eq92 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq x.toUInt32 92) = if x.toNat = 92 then 1 else 0 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem ne34 (x : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ne x.toUInt32 34) = if x.toNat = 34 then 0 else 1 := by
  revert x; exact SerdeRead.uint8_forall (by decide +kernel)

theorem costErr_mono (cfg : WasmConfig) (F i j : Nat) (h : i ≤ j) : costErr cfg F i ≤ costErr cfg F j := by
  unfold costErr SerdePosition.cost638 SerdePosition.cost645
  have := Nat.mul_le_mul_right cfg.regularOpCost (show 80 + (40 + (200 + 50 * i)) ≤ 80 + (40 + (200 + 50 * j)) by omega)
  omega

section L646

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`SliceRead::parse_str(out, rd, scratch)`** (646) on an escape-free input: from `i`, the plain
bytes `body`, then `tail`, empty or starting with a byte that stops the scan and is not `\`; the
scratch empty. The result is `res646`, at `cost646`. -/
theorem f646_spec_noesc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr idx : UInt32) (ob bs body tail : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (_hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 160 ≤ sp.toNat) (hi : i ≤ bs.length) (hsplit : bs.drop i = body ++ tail)
    (hplain : ∀ b ∈ body, plain b = true)
    (hstop : ∀ x rest, tail = x :: rest → plain x = false ∧ x ≠ 0x5C)
    (hr : roomFor4 mlen maxP 20) :
    errCode n maxP inst mi A ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗
      A 657 ↪[wf] FuncInst.wasm types[31]! inst f657 ∗ A 647 ↪[wf] FuncInst.wasm types[31]! inst f647 ∗
      A 648 ↪[wf] FuncInst.wasm types[45]! inst f648 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 160) 160 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width))
        (fun _ => cost646 cfg F i body tail)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ res646 n maxP mlen live F out de ptr ob bs body tail i)) := by
  iintro ⟨Hcode, #F927, #F657, #F647, #F648⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #F583, #H609, #H645, #H638⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha583 := hm.funcs 583 (by decide)
  have ha647 := hm.funcs 647 (by decide)
  have ha648 := hm.funcs 648 (by decide)
  have ha927 := hm.funcs 927 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t36 : types[36]!.params.length = 6 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hsc, He, Hw⟩
  subst hargs
  have hil : i + body.length ≤ bs.length := by
    have := congrArg List.length hsplit; simp at this; omega
  have htl : i + body.length + tail.length = bs.length := by
    have := congrArg List.length hsplit; simp at this; omega
  have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat i)) = 0
      then Value.i32 (UInt32.ofNat i) else Value.i32 (UInt32.ofNat bs.length)) = Value.i32 (UInt32.ofNat bs.length) := by
    by_cases hib : i = bs.length
    · rw [hib]; split <;> rfl
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat i)) ≠ 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      rw [if_neg this]
  have hlt := sp.toNat_lt
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  simp only [f646, cost646]
  generalize hE : (if ok646 body tail then 0 else costErr cfg F (i + body.length + 1)) = E
  generalize hK : cost927 body.length * cfg.regularOpCost = K
  rw [show (330 + 30 * body.length + cost927 body.length) * cfg.regularOpCost + E + R =
    60 * cfg.regularOpCost + ((270 + 30 * body.length) * cfg.regularOpCost + (K + (E + R))) by
      rw [← hK]; simp only [Nat.add_mul]; omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  generalize hW : (270 + 30 * body.length) * cfg.regularOpCost = W
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 54 * cfg.regularOpCost + (W + (K + (E + R))))
    (I := fun X fr => iprop(⌜X = [] ∧ fr = fr646 inst mi out de sc (sp - 48) 0 0 0 0 0 0⌝ ∗
      credits Cg (54 * cfg.regularOpCost + (W + (K + (E + R)))) ∗ stk n (sp.toNat - 160) 160 ∗
      n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗ n ↦[wms][ 1062392 ] escTable ∗
      n ↦[wms][ 1071704 ] utf8Width ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
      n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
      n ↦[i32][ de.toNat + 8 ] UInt32.ofNat i ∗ n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%⟨hX, hfr⟩, Hc, Hs, Ho, Hsc, He, Hw, Hvt, Hh, D0, D4, D8, Hb, Hg⟩
    subst hX
    rw [hfr]
    simp only [fr646]
    clear hfr
    mstep; mstep [D4]; mstep; mstep; mstep [D8]
    mstep; mstep; mstep; mstep
    iapply mwpi_cons
    iapply FromUtf8.mwpi_select'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; omega
    inext
    iintro Hc
    rw [hsel]
    clear hsel
    mctrl_norm
    mstep; mstep; mstep [D0]; mstep; mstep; mstep
    mstep; mstep
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 30 * (i + body.length - i) * cfg.regularOpCost + 260 * cfg.regularOpCost + (K + (E + R)))
      (I := invS n inst mi Cg cfg.regularOpCost 260 (K + (E + R)) out de sc (sp - 48) (UInt32.ofNat bs.length) (UInt32.ofNat i)
        (UInt32.ofNat bs.length) ptr i body.length
        iprop(stk n (sp.toNat - 160) 160 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[i32][ de.toNat ] ptr ∗
          n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
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
      icases HP with ⟨Hs, Ho, Hsc, He, Hw, Hvt, Hh, D0, D4, Hb, Hg⟩
      by_cases hkl : k < bs.length
      · have hne : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat bs.length) (UInt32.ofNat k)) = 0 := by
          have hu : (UInt32.ofNat k).toNat = k := by simp; omega
          have hv : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
          generalize UInt32.ofNat k = u at hu ⊢
          generalize UInt32.ofNat bs.length = v at hv ⊢
          have : v ≠ u := fun e => by subst e; omega
          simp [Numeric.bool, Numeric.irelop32, this]
        have hbk : bs[k]? = (body ++ tail)[k - i]? := by
          rw [← hsplit, List.getElem?_drop]; congr 1; omega
        ihave Hb := MemCpy.memBytes_pick n ptr.toNat k bs hkl $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
        rw [hxk]
        rw [List.getElem?_eq_getElem hkl, hxk] at hbk
        have es : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
        have hx256 := x.toNat_lt
        by_cases hkm' : k < i + body.length
        · have hxb : plain x = true := by
            rw [List.getElem?_append_left (by omega)] at hbk
            exact hplain x (List.mem_of_getElem? hbk.symm)
          rw [show 30 * (i + body.length - k) * cfg.regularOpCost + 260 * cfg.regularOpCost + (K + (E + R)) =
            290 * cfg.regularOpCost + (30 * (i + body.length - (k + 1)) * cfg.regularOpCost + (K + (E + R))) by
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
          iapply invS_intro n inst mi Cg cfg.regularOpCost 260 (K + (E + R)) out de sc (sp - 48) _ _ _ ptr i body.length _ (k + 1) _
            (by omega) (by omega)
          iframe D8 Hs Ho Hsc He Hw Hvt Hh D0 D4 Hb Hg
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · -- the scan stops at `x`, the first byte of `tail`
          have hk : k = i + body.length := by omega
          have htx : ∃ rest, tail = x :: rest := by
            rw [List.getElem?_append_right (by omega), show k - i - body.length = 0 by omega] at hbk
            cases htl' : tail with
            | nil => rw [htl'] at hbk; simp at hbk
            | cons y rest => rw [htl'] at hbk; simp at hbk; exact ⟨rest, by simp [hbk]⟩
          obtain ⟨rest, htx⟩ := htx
          obtain ⟨hxp, hx5c⟩ := hstop x rest htx
          have hx92 : x.toNat ≠ 92 := fun e => hx5c (UInt8.toNat_inj.mp (by rw [e]; rfl))
          have h92 : Numeric.bool (Numeric.irelop32 IRelOp.eq x.toUInt32 92) = 0 := by rw [eq92, if_neg hx92]
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
          rw [SerdeKey.load8, esc_at, if_neg (by rw [hxp]; decide)]
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
          have h48 : (sp - 48).toNat = sp.toNat - 48 := by
            rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
          mstep; mstep; mstep; mstep
          brn h92
          by_cases hx34 : x.toNat = 34
          · -- `"`: the end of the string, the scratch empty
            have hx : x = 0x22 := UInt8.toNat_inj.mp (by rw [hx34]; rfl)
            have hsplit' : bs.drop i = body ++ 0x22 :: rest := by rw [hsplit, htx, hx]
            rw [hx]
            icases stk_split n (sp.toNat - 160) 112 48 $$ Hs with ⟨S112, S48⟩
            rw [show sp.toNat - 160 + 112 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 8 40 $$ S48 with ⟨S8, S40⟩
            icases stk_split n ((sp - 48).toNat + 8) 24 16 $$ S40 with ⟨S24, S16⟩
            icases stk_split n ((sp - 48).toNat + 8 + 24) 12 4 $$ S16 with ⟨S12, S4⟩
            iunfold stk at S8 S12
            icases S8 with ⟨%s8, %hs8, S8⟩
            icases S12 with ⟨%s12, %hs12, S12⟩
            mstep; mstep; mstep
            brn (by decide)
            mstep; mstep
            mstep [Hsc]
            brn rfl
            mstep; mstep; mstep; mstep; mstep; mstep
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
            have h32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
            have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
            by_cases hutf : Utf8.utf8Ok body = true
            · -- the body is UTF-8: `Ok(Borrowed)`
              have hok : ok646 body tail := ⟨by rw [htx, hx]; rfl, hutf⟩
              rw [if_pos hok] at hE
              subst hE
              ihave Hb := U128From.memBytes_split n ptr.toNat i bs (by omega) $$ Hb
              icases Hb with ⟨B0, Bd⟩
              rw [hsplit']
              ihave Bd := U128From.memBytes_split n (ptr.toNat + i) body.length (body ++ 0x22 :: rest) (by simp) $$ Bd
              icases Bd with ⟨Bbody, Brest⟩
              rw [List.take_left' rfl, List.drop_left' rfl]
              ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + i = (ptr + UInt32.ofNat i).toNat by
                simp [UInt32.toNat_add]; omega) $$ Bbody
              ihave S12 := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ S12
              icases stk_split n (sp.toNat - 160) 80 32 $$ S112 with ⟨S80, S32⟩
              ihave S32 := stk_addr (show sp.toNat - 160 + 80 = (sp - 48).toNat - 32 by omega) $$ S32
              have hK3 : (12 + cost648 (UInt32.ofNat body.length).toNat) * cfg.regularOpCost = 52 * cfg.regularOpCost + K := by
                rw [hm32, ← hK]; unfold cost648; simp only [Nat.add_mul]; omega
              mcall (f648_spec_valid cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg (A 927) ha927 (by omega) Cg gt
                (sp - 48) (sp - 48 + 32) de (ptr + UInt32.ofNat i) (UInt32.ofNat body.length) s12 body hs12
                (by rw [UInt32.toNat_add, h48]; simp; omega) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
                (by omega) hutf) using [Hg S32 S12 Bbody Hw]
              · iframe Hg S32 S12 Bbody Hw
              rw [hK3]
              mcredits (60 * cfg.regularOpCost + R)
              icases HQ with ⟨%hrs, Hg, S32, Q0, Q4, Q8, Bbody, Hw⟩
              subst hrs
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
              iframe Hg Hvt Hsc He Hw
              isplitr [Hh O0 O4 O8 O12 D0 D4 D8 B0 Bbody Brest]
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
                ihave S80' := stk_join n ((sp - 48).toNat - 32) 32 48 $$ [S32 S48]
                · rw [show (sp - 48).toNat - 32 + 32 = (sp - 48).toNat by omega]; iframe S32 S48
                ihave S80' := stk_addr (show (sp - 48).toNat - 32 = sp.toNat - 160 + 80 by omega) $$ S80'
                iapply stk_join n (sp.toNat - 160) 80 80
                iframe S80 S80'
              iunfold res646
              rw [if_pos hok]
              iframe Hh
              rw [show out.toNat + 4 + 4 + 4 = out.toNat + 12 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
              iframe O0 O4 O8 O12
              iunfold rd, sliceRead
              rw [show i + body.length + 1 = k + 1 by omega]
              iframe D0 D4 D8
              ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat i).toNat = ptr.toNat + i by
                simp [UInt32.toNat_add]; omega) $$ Bbody
              ihave Bd := U128From.memBytes_join n (ptr.toNat + i) body.length body (34 :: rest) rfl $$ [Bbody Brest]
              · iframe Bbody Brest
              rw [← hsplit']
              ihave Bb := U128From.memBytes_join n ptr.toNat i (bs.take i) (bs.drop i) (by simp; omega) $$ [B0 Bd]
              · iframe B0 Bd
              rw [List.take_append_drop]
              iexact Bb
            · -- the body is not UTF-8: `as_str` fails (657)
              have hbad : Utf8.utf8Ok body = false := by simpa using hutf
              have hnok : ¬ ok646 body tail := fun h => hutf h.2
              rw [if_neg hnok] at hE
              icases U128From.memBytes_split n ((sp - 48).toNat + 8 + 24) 8 s12 (by omega) $$ S12 with ⟨S12a, S12b⟩
              ihave S12a := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ S12a
              ihave Hrd : rd n de ptr bs (i + body.length + 1) $$ [D0 D4 D8 Hb]
              · iunfold rd, sliceRead; rw [show i + body.length + 1 = k + 1 by omega]; iframe D0 D4 D8 Hb
              ihave S112 := stk_addr (show sp.toNat - 160 = (sp - 48).toNat - 112 by omega) $$ S112
              have key := f648_spec_bad (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
                (sp - 48) (sp - 48 + 32) de ptr (ptr + UInt32.ofNat i) (UInt32.ofNat body.length) idx (s12.take 8) bs
                (i + body.length + 1) i maxP mlen live F (by simp; omega) (by rw [h32]; omega) hde (by omega) hlen hptr
                (by simp [UInt32.toNat_add]; omega) (by rw [hm32]; omega)
                (by rw [hm32, hsplit, List.take_left' rfl]; exact hbad) (by omega) hr
              rw [hm32, hE, Nat.add_mul, hK] at key
              unfold errCode at key
              mcall key using [Hg S112 Hvt Hh S12a Hrd Hw]
              · iframe Hg S112 Hvt Hh S12a Hrd Hw
              clear key
              mcredits (30 * cfg.regularOpCost + R)
              icases HQ with ⟨%hrs, %q, %hq, Hg, S112, Hvt, HA, Q0, Q4, Hrd, Hw⟩
              subst hrs
              rw [h32]
              icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
              icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
              mstep; mstep [Q4]; mstep
              mstep; mstep; mstep [Q0]; mstep; mstep
              iapply mwpi_cons
              iapply mwpi_br_if_taken'
              isplitr
              · ipureintro; exact ⟨rfl, by decide⟩
              mctrl_norm
              repeat mpay
              mstep; mstep; mstep [O0]
              mstep; mstep; mstep [O4]
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
              iframe Hg Hvt Hsc He Hw
              isplitr [HA O0 O4 O8 Hrd]
              · ihave P0 := stk_word n (sp - 48).toNat _ $$ P0
                ihave P4 := stk_word n ((sp - 48).toNat + 4) _ $$ P4
                ihave P8 := stk_join n (sp - 48).toNat 4 4 $$ [P0 P4]
                · iframe P0 P4
                ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
                ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
                ihave Q8 := stk_join n ((sp - 48).toNat + 32) 4 4 $$ [Q0 Q4]
                · iframe Q0 Q4
                ihave S12b := stk_intro n _ _ $$ S12b
                rw [show (s12.drop 8).length = 4 by simp; omega]
                ihave S12b := stk_addr (show (sp - 48).toNat + 8 + 24 + 8 = (sp - 48).toNat + 32 + 8 by omega) $$ S12b
                ihave Q12 := stk_join n ((sp - 48).toNat + 32) 8 4 $$ [Q8 S12b]
                · iframe Q8 S12b
                ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [P8 S24]
                · iframe P8 S24
                ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                · iframe S32' Q12
                ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 S4]
                · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 S4
                ihave S112 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 160 by omega) $$ S112
                ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 160 + 112 by omega) $$ S48
                iapply stk_join n (sp.toNat - 160) 112 48
                iframe S112 S48
              iunfold res646
              rw [if_neg hnok, if_neg (by rw [htx]; simp)]
              iexists q
              isplitr
              · ipureintro; exact hq
              rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop],
                show out.toNat + 4 + 4 = out.toNat + 8 by omega]
              iframe HA O0 O4 O8 Hrd
          · -- a control byte: `ControlCharacterWhileParsingString`
            have hnok : ¬ ok646 body tail := by
              intro ⟨h1, _⟩; rw [htx] at h1; simp at h1; exact hx34 (by rw [h1]; rfl)
            rw [if_neg hnok] at hE
            have h34 : Numeric.bool (Numeric.irelop32 IRelOp.ne x.toUInt32 34) ≠ 0 := by rw [ne34, if_neg hx34]; decide
            mstep; mstep; mstep
            iapply mwpi_cons
            iapply mwpi_br_if_taken'
            isplitr
            · ipureintro; exact ⟨rfl, h34⟩
            mctrl_norm
            repeat mpay
            mstep; mstep; mstep; mstep
            mstep [D8]
            rw [SerdeRead.ofNat_succ k (by omega)]
            icases stk_split n (sp.toNat - 160) 112 48 $$ Hs with ⟨S112, S48⟩
            icases stk_split n (sp.toNat - 160) 32 80 $$ S112 with ⟨S32, S80⟩
            rw [show sp.toNat - 160 + 112 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 32 16 $$ S48 with ⟨SF, S16⟩
            icases stk_split n ((sp - 48).toNat + 32) 4 12 $$ S16 with ⟨SC0, S12⟩
            icases stk_split n ((sp - 48).toNat + 32 + 4) 8 4 $$ S12 with ⟨SC8, S4⟩
            iunfold stk at SC0 SC8
            icases SC0 with ⟨%sc0, %hsc0, SC0⟩
            icases SC8 with ⟨%sc8, %hsc8, SC8⟩
            mstep; mstep
            mstep [SC0] with (simp [UInt32.toNat_add]; omega)
            mstep; mstep; mstep; mstep; mstep
            ihave C := U128From.memBytes_join n ((sp - 48).toNat + 32) 4 (bytes32 15) sc8 (by simp) $$ [SC0 SC8]
            · iframe SC0 SC8
            ihave C := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 32 = (sp - 48 + 32).toNat by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ C
            ihave S80 := stk_addr (show sp.toNat - 160 + 32 = (sp - 48).toNat - 80 by omega) $$ S80
            icases U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨O8, O16⟩
            have key := f647_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
              (sp - 48) out de (sp - 48 + 32) ptr idx (ob.take 8) (bytes32 15 ++ sc8) bs (k + 1) maxP mlen live F
              (by simp; omega) (by omega) (by simp; omega) (by rw [UInt32.toNat_add, h48]; simp; omega) hde (by omega)
              hlen hptr (by omega) hr
            rw [hk, hE] at key
            unfold errCode at key
            mcall key using [Hg S80 Hvt Hh O8 C D0 D4 D8 Hb]
            · iframe Hg S80 Hvt Hh O8 C
              iunfold rd, sliceRead
              rw [hk]
              iframe D0 D4 D8 Hb
            clear key
            mcredits (20 * cfg.regularOpCost + R)
            icases HQ with ⟨%hrs, %p, %hp, Hg, S80, Hvt, HA, O0, O4, C, Hrd⟩
            subst hrs
            mstep; mstep; mstep; mstep [Hg]
            rw [show sp - 48 + 48 = sp by simp]
            repeat mstep
            isplitl [Hc]
            · iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
            isplitr
            · ipureintro; trivial
            iframe Hg Hvt Hsc He Hw
            isplitr [HA O0 O4 O16 Hrd]
            · ihave C := stk_intro n _ _ $$ C
              rw [show (bytes32 15 ++ sc8).length = 12 by simp; omega]
              ihave C := stk_addr (show (sp - 48 + 32).toNat = (sp - 48).toNat + 32 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ C
              ihave J1 := stk_join n ((sp - 48).toNat + 32) 12 4 $$ [C S4]
              · rw [show (sp - 48).toNat + 32 + 12 = (sp - 48).toNat + 32 + 4 + 8 by omega]; iframe C S4
              ihave J2 := stk_join n (sp - 48).toNat 32 16 $$ [SF J1]
              · iframe SF J1
              ihave S80 := stk_addr (show (sp - 48).toNat - 80 = sp.toNat - 160 + 32 by omega) $$ S80
              ihave J3 := stk_join n (sp.toNat - 160) 32 80 $$ [S32 S80]
              · iframe S32 S80
              ihave J2 := stk_addr (show (sp - 48).toNat = sp.toNat - 160 + 112 by omega) $$ J2
              iapply stk_join n (sp.toNat - 160) 112 48
              iframe J3 J2
            iunfold res646
            rw [if_neg hnok, if_neg (by rw [htx]; simp)]
            iexists p
            isplitr
            · ipureintro; exact hp
            rw [← hk]
            iframe HA O0 O4 O16 Hrd
      · -- EOF: the scan reaches the end of the input
        have hk : k = bs.length := by omega
        have hj : i + body.length = bs.length := by omega
        have htn : tail = [] := by rw [← List.length_eq_zero_iff]; omega
        have hnok : ¬ ok646 body tail := by simp [ok646, htn]
        rw [if_neg hnok] at hE
        subst hk
        rw [show 30 * (i + body.length - bs.length) * cfg.regularOpCost = 0 by
          rw [show i + body.length - bs.length = 0 by omega]; simp, Nat.zero_add]
        have heq : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat bs.length) (UInt32.ofNat bs.length)) ≠ 0 := by
          simp [Numeric.bool, Numeric.irelop32]
        have hlu : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat bs.length) (UInt32.ofNat i)) = 0 := by
          simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
        have h48 : (sp - 48).toNat = sp.toNat - 48 := by
          rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
        mstep; mstep; mstep
        iapply mwpi_cons
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, heq⟩
        mctrl_norm
        simp only [Post.mloop]
        mctrl_norm
        repeat mpay
        mstep; mstep; mstep
        brn hlu
        icases stk_split n (sp.toNat - 160) 112 48 $$ Hs with ⟨S112, S48⟩
        icases stk_split n (sp.toNat - 160) 32 80 $$ S112 with ⟨S32, S80⟩
        rw [show sp.toNat - 160 + 112 = (sp - 48).toNat by omega]
        icases stk_split n (sp - 48).toNat 32 16 $$ S48 with ⟨SF, S16⟩
        icases stk_split n ((sp - 48).toNat + 32) 4 12 $$ S16 with ⟨SC0, S12⟩
        icases stk_split n ((sp - 48).toNat + 32 + 4) 8 4 $$ S12 with ⟨SC8, S4⟩
        iunfold stk at SC0 SC8
        icases SC0 with ⟨%sc0, %hsc0, SC0⟩
        icases SC8 with ⟨%sc8, %hsc8, SC8⟩
        mstep; mstep
        mstep [SC0] with (simp [UInt32.toNat_add]; omega)
        mstep; mstep; mstep; mstep; mstep
        ihave C := U128From.memBytes_join n ((sp - 48).toNat + 32) 4 (bytes32 4) sc8 (by simp) $$ [SC0 SC8]
        · iframe SC0 SC8
        ihave C := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 32 = (sp - 48 + 32).toNat by
          rw [UInt32.toNat_add, h48]; simp; omega) $$ C
        ihave S80 := stk_addr (show sp.toNat - 160 + 32 = (sp - 48).toNat - 80 by omega) $$ S80
        icases U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨O8, O16⟩
        have key := f647_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
          (sp - 48) out de (sp - 48 + 32) ptr idx (ob.take 8) (bytes32 4 ++ sc8) bs bs.length maxP mlen live F
          (by simp; omega) (by omega) (by simp; omega) (by rw [UInt32.toNat_add, h48]; simp; omega) hde le_rfl
          hlen hptr (by omega) hr
        have key2 := key.trans (AllocGen.MFunSpec_cost (K' := fun _ => E)
          (fun _ => by rw [← hE]; exact costErr_mono cfg F _ _ (by omega)))
        unfold errCode at key2
        mcall key2 using [Hg S80 Hvt Hh O8 C D0 D4 D8 Hb]
        · iframe Hg S80 Hvt Hh O8 C
          iunfold rd, sliceRead
          iframe D0 D4 D8 Hb
        clear key key2
        mcredits (20 * cfg.regularOpCost + R)
        icases HQ with ⟨%hrs, %p, %hp, Hg, S80, Hvt, HA, O0, O4, C, Hrd⟩
        subst hrs
        mstep
        mstep; mstep; mstep; mstep [Hg]
        rw [show sp - 48 + 48 = sp by simp]
        repeat mstep
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        isplitr
        · ipureintro; trivial
        iframe Hg Hvt Hsc He Hw
        isplitr [HA O0 O4 O16 Hrd]
        · ihave C := stk_intro n _ _ $$ C
          rw [show (bytes32 4 ++ sc8).length = 12 by simp; omega]
          ihave C := stk_addr (show (sp - 48 + 32).toNat = (sp - 48).toNat + 32 by
            rw [UInt32.toNat_add, h48]; simp; omega) $$ C
          ihave J1 := stk_join n ((sp - 48).toNat + 32) 12 4 $$ [C S4]
          · rw [show (sp - 48).toNat + 32 + 12 = (sp - 48).toNat + 32 + 4 + 8 by omega]; iframe C S4
          ihave J2 := stk_join n (sp - 48).toNat 32 16 $$ [SF J1]
          · iframe SF J1
          ihave S80 := stk_addr (show (sp - 48).toNat - 80 = sp.toNat - 160 + 32 by omega) $$ S80
          ihave J3 := stk_join n (sp.toNat - 160) 32 80 $$ [S32 S80]
          · iframe S32 S80
          ihave J2 := stk_addr (show (sp - 48).toNat = sp.toNat - 160 + 112 by omega) $$ J2
          iapply stk_join n (sp.toNat - 160) 112 48
          iframe J3 J2
        iunfold res646
        rw [if_neg hnok, if_pos htn, Nat.add_zero, hj]
        iexists p
        isplitr
        · ipureintro; exact hp
        iframe HA O0 O4 O16 Hrd
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; rw [← hW]; simp only [Nat.add_mul, Nat.add_sub_cancel_left]; omega
    inext
    iintro Hc
    iapply invS_intro n inst mi Cg cfg.regularOpCost 260 (K + (E + R)) out de sc (sp - 48) _ _ _ ptr i body.length _ i _
      le_rfl (by omega)
    iframe Hc D8 Hs Ho Hsc He Hw Hvt Hh D0 D4 Hb Hg
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iframe Hc Hs Ho Hsc He Hw Hvt Hh D0 D4 D8 Hb Hg
  ipureintro; exact ⟨rfl, rfl⟩

end L646

end WNear.Binary.ParseStr

/-! ## The model side -/

namespace WNear.Binary.ParseStr

open NearInterface.Json (stringBody)

/-- `stringBody` skips plain bytes, accumulating them. -/
theorem stringBody_skip (body tail acc : List UInt8) (h : ∀ b ∈ body, plain b = true) :
    stringBody (body ++ tail) acc = stringBody tail (body.reverse ++ acc) := by
  induction body generalizing acc with
  | nil => simp
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

/-- **646 against the model, escape-free inputs.** When 646 accepts (`ok646`), `stringBody` decodes
the string whose bytes are `body` and leaves the rest past the `"`; when 646 fails (EOF, a control
byte, a body that is not UTF-8), `stringBody` decodes no string: `none`, or `some (none, _)`, which
every typed string (a field, a key) rejects. -/
theorem noesc_model (bs body tail : List UInt8) (i : Nat) (hsplit : bs.drop i = body ++ tail)
    (hplain : ∀ b ∈ body, plain b = true)
    (hstop : ∀ x rest, tail = x :: rest → plain x = false ∧ x ≠ 0x5C) :
    if ok646 body tail then
      ∃ s : String, ∃ rest, tail = 0x22 :: rest ∧ stringBody (bs.drop i) [] = some (some s, rest) ∧
        s.toByteArray = body.toByteArray
    else ∀ s rest, stringBody (bs.drop i) [] ≠ some (some s, rest) := by
  split
  · next hok =>
    obtain ⟨h1, hutf⟩ := hok
    obtain ⟨rest, htr⟩ : ∃ rest, tail = 0x22 :: rest := by
      cases tail with
      | nil => simp at h1
      | cons y r => simp at h1; exact ⟨r, by rw [h1]⟩
    subst htr
    · obtain ⟨s, hs, hb⟩ := utf8_model bs body rest i hsplit hplain hutf
      exact ⟨s, rest, rfl, hs, hb⟩
  · next hnok =>
    intro s rest
    rw [hsplit, stringBody_skip body tail [] hplain]
    match tail, hstop, hnok with
    | [], _, _ => simp [stringBody]
    | x :: r, hstop, hnok =>
      obtain ⟨hxp, hx5c⟩ := hstop x r rfl
      by_cases hx : x = 0x22
      · subst hx
        have hbad : Utf8.utf8Ok body = false := by
          cases h : Utf8.utf8Ok body
          · rfl
          · exact absurd ⟨rfl, h⟩ hnok
        have hn := Utf8.fromUTF8?_isSome body
        rw [hbad] at hn
        rw [stringBody.eq_2]
        simp only [List.append_nil, List.reverse_reverse]
        rw [Option.isSome_eq_false_iff.mp hn |> Option.isNone_iff_eq_none.mp]
        simp
      · have hlt : x < 0x20 := by
          simp only [plain, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.and_eq_false_imp] at hxp
          apply UInt8.lt_iff_toNat_lt.mpr
          have e22 : x.toNat ≠ 0x22 := fun e => hx (UInt8.toNat_inj.mp (by rw [e]; rfl))
          have e5c : x.toNat ≠ 0x5C := fun e => hx5c (UInt8.toNat_inj.mp (by rw [e]; rfl))
          simp; by_contra hc; exact absurd (hxp (by omega)) (by simp; omega)
        rw [stringBody.eq_13 _ _ _ hx (fun _ _ e _ => hx5c e), if_pos hlt]
        simp

end WNear.Binary.ParseStr
