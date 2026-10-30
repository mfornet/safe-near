import Bridge.Functions.SerdeNextKey

/-!
# serde's `next_element_seed` for `ft_balance_of`'s struct: 214 (M6)

The array form `["<a>"]` of the struct reads its one element with `SeqAccess::next_element_seed`
(214). The sequence access at `acc` is the `Deserializer` pointer `de` and the `first` byte at
`acc + 4`.

```wat
;; 214 (out, acc)       ws (339); Err → out := Err; None → EofWhileParsingList (2)
;;   ']'                → out := Ok(None)
;;   ',' with first = 0 → eat, ws; then the byte below (None → EofWhileParsingValue)
;;   ',' with first = 1, or another byte with first = 1 → first := 0, the byte below
;;   another byte with first = 0 → ExpectedListCommaOrEnd (7)
;;   the byte: ']' → TrailingComma (18); else ValidAccountId::deserialize (169) into the frame,
;;             then out := Ok(Some(v)) or Err(e)
```

The struct calls it once, with `first = 1`. The accepting case (`f214_first`): after the whitespace
a byte `b ≠ ]`, the value read by 169 at that byte, taken as the hypothesis `Spec169` (its `Ok`
`String (p, c, l)` in 214's frame), and `Ok(Some((p, c, l)))` at `out`. When `fromSlice` accepts the
array form, `SerdeStructModel.structDe` reads the element exactly there (`dv (skipWhitespace rest)`,
after `[` and a byte that is not `]`).
-/

namespace WNear.Binary.SerdeSeqElem

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit)

set_option maxRecDepth 100000 in
theorem eq_is44 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 44) = if b = 44 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem ne_is93 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ne b.toUInt32 93) = if b = 93 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

section L214

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The specification of `ValidAccountId::deserialize` (169) that 214 needs at the reader's index
`j`: called with 214's frame `sp - 16` as `out`, it returns `Ok(String (p, c, l))` there, `p ≠ 0`.
`P169` and `Q169 p c l` carry the rest of its state (the stack below, the heap, the reader). -/
def Spec169 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (Cg : Nat) (gt : GlobalType) (sp de ptr : UInt32) (ob bs : List UInt8) (j : Nat)
    (P169 : IProp GF) (K169 : Nat) (Q169 : UInt32 → UInt32 → UInt32 → IProp GF) : IProp GF :=
  MFunSpec cfg lim d types[14]! inst mi f169 Cg
    (fun args => iprop(⌜args = [.i32 (sp - 16), .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
      n ↦[wms][ (sp - 16).toNat ] ob ∗ rd n de ptr bs j ∗ P169))
    (fun _ => K169)
    (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
      ∃ (p c l : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ (sp - 16).toNat ] 0 ∗ n ↦[i32][ (sp - 16).toNat + 4 ] p ∗
        n ↦[i32][ (sp - 16).toNat + 8 ] c ∗ n ↦[i32][ (sp - 16).toNat + 12 ] l ∗ Q169 p c l))

instance (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (Cg : Nat) (gt : GlobalType) (sp de ptr : UInt32) (ob bs : List UInt8) (j : Nat)
    (P169 : IProp GF) (K169 : Nat) (Q169 : UInt32 → UInt32 → UInt32 → IProp GF) :
    Persistent (Spec169 cfg lim d inst mi n g Cg gt sp de ptr ob bs j P169 K169 Q169) := by
  unfold Spec169; infer_instance

set_option hygiene false in
/-- From `block` (the element's byte test) to the end of 214: the byte `b ≠ ]`, then 169 and the
copy of its `Ok` to `out`. -/
local macro "elem_tail" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep
  mstep_taken with (rw [ne_is93, if_neg hb93]; decide)
  mstep; mstep; mstep [Hacc]
  mcall S169 using [Hg Hob Hrd HP]
  · iframe Hg Hob Hrd HP
  icases HQ with ⟨%hrs, Hg, %p, %c, %l, %hp, W0, W4, W8, W12, HQ⟩
  subst hrs
  mcredits (60 * cfg.regularOpCost + R)
  mstep; mstep; mstep [W0]; mstep; mstep
  mstep_taken with decide
  ihave W4 := KeyGet.join64 n ((sp - 16).toNat + 4) p c $$ [W4 W8]
  · rw [show (sp - 16).toNat + 4 + 4 = (sp - 16).toNat + 8 by omega]; iframe W4 W8
  mstep; mstep
  mstep [W4] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.ofNat_decode_pair]
  mstep [O4] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [W12] with (simp [UInt32.toNat_add]; omega)
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hacc Hg
  isplitl [Hfb]
  · first | iexact Hfb | (iapply SerdeNextKey.store0; iexact Hfb)
  ihave W4 := KeyGet.split64 n ((sp - 16).toNat + 4) p c $$ W4
  icases W4 with ⟨W4, W8⟩
  ihave W0 := stk_word $$ W0
  ihave W4 := stk_word $$ W4
  ihave W8 := stk_word $$ W8
  ihave W12 := stk_word $$ W12
  rw [show (sp - 16).toNat + 4 + 4 = (sp - 16).toNat + 8 by omega]
  ihave F16 := VecFromElem.stk16_join n (sp - 16).toNat $$ [W0 W4 W8 W12]
  · iframe W0 W4 W8 W12
  rw [h16]
  iframe F16
  iexists p
  iexists c
  iexists l
  ihave O4 := KeyGet.split64 n (out.toNat + 4) p c $$ O4
  icases O4 with ⟨O4, O8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe O0 O4 O8 O12 HQ
  ipureintro; exact hp))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **214 at the struct's one element**: `first = 1`, and after the whitespace a byte `b ≠ ]`;
169 there (the hypothesis `Spec169`) returns `Ok(String (p, c, l))`, and `out` gets
`Ok(Some((p, c, l)))`, `first` cleared. -/
theorem f214_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out acc de ptr : UInt32) (ob ob2 bs : List UInt8) (i : Nat) (b : UInt8)
    (maxP : Nat) (hob : ob.length = 16) (hob2 : ob2.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 16 ≤ sp.toNat) (hi : i ≤ bs.length)
    (hb : bs[i + wsLen (bs.drop i)]? = some b) (hb93 : b ≠ 0x5D)
    (P169 : IProp GF) (K169 : Nat) (Q169 : UInt32 → UInt32 → UInt32 → IProp GF) :
    endCode n maxP inst mi A ∗ A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
      Spec169 cfg lim (d + 1) inst mi n g Cg gt sp de ptr ob bs (i + wsLen (bs.drop i)) P169 K169 Q169 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f214 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [1] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ (sp - 16).toNat ] ob ∗
          n ↦[wms][ out.toNat ] ob2 ∗ rd n de ptr bs i ∗ P169))
        (fun _ => (300 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + K169)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [0] ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 16) 16 ∗
          ∃ (p c l : UInt32), ⌜p ≠ 0⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] l ∗ Q169 p c l)) := by
  iintro ⟨#Hv, #F169, #S169⟩
  iunfold Spec169 at S169
  iunfold endCode at Hv
  icases Hv with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha169 := hm.funcs 169 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hacc, Hfb, Hg, Hob, Ho, Hrd, HP⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases U128From.memBytes_split n out.toNat 4 ob2 (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob2.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
  rw [show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  generalize hw : wsLen (bs.drop i) = w at hb key ⊢
  generalize hj : i + w = j at hb key ⊢
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W at key
  rw [show (300 + 96 * w) * cfg.regularOpCost + K169 + R =
    100 * cfg.regularOpCost + (W + (100 * cfg.regularOpCost + (K169 + R))) by
      rw [← hW]; simp only [Nat.add_mul]; omega]
  simp only [f214]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mstep [Hacc]
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (180 * cfg.regularOpCost + (K169 + R))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb]
  generalize hob' : optByte (some b) = obv
  have hok1 : Numeric.bool (obv &&& 1 == 0) = 1 := by rw [← hob']; simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with (rw [← hob']; exact some_bit b)
  rw [← hob']
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  by_cases h44 : b = 44
  · mstep_taken with (rw [eq_is44, if_pos h44]; decide)
    mstep; mstep [Hfb]
    mstep_taken with decide
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    mstep; mstep; mstep [Hfb]; mstep
    elem_tail
  · mstep_not_taken with (rw [eq_is44, if_neg h44])
    mstep; mstep; mstep
    mstep_taken with (rw [ne_is93, if_neg hb93]; decide)
    mstep; mstep [Hfb]; mstep
    mstep_not_taken with decide
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    mstep; mstep; mstep [Hfb]; mstep
    elem_tail

end L214

end WNear.Binary.SerdeSeqElem
