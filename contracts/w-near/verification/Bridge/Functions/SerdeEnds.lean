import Bridge.Functions.SerdeDeStr

/-!
# serde_json's punctuation checks: `end` (320), `parse_object_colon` (89), `end_map` (90) (M6)

Each skips whitespace (339), peeks one byte and either eats it or builds a syntax error with
`peek_error` (322). They return the error box, or 0.

```wat
;; 320 end(de)                 ws; None → 0; Some _ → peek_error(TrailingCharacters = 19)
;; 89 parse_object_colon(de)   ws; ':' → eat, 0; None → EofWhileParsingObject (3); _ → ExpectedColon (6)
;; 90 end_map(de)              ws; '}' → eat, 0; None → 3; ',' → TrailingComma (18); _ → 19
```

The reader is `rd n de ptr bs i`. With `j = i + wsLen (bs.drop i)` the index after the whitespace,
each spec gives:

* on the accepted byte (none for 320, `:` for 89, `}` for 90): the result 0, the heap unchanged, the
  reader at `j` (320) or `j + 1`;
* otherwise: a box `p ≠ 0` (`heapA`), the reader at `j`.

The cost is `(K + 96·w)·c` with `w` the whitespace's length, plus `costErr cfg F (j + 1) + 20·c` on
an error.
-/

namespace WNear.Binary.SerdeEnds

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code the punctuation checks run (persistent). -/
def endCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(errCode n maxP inst mi A ∗ A 640 ↪[wf] FuncInst.wasm types[14]! inst f640 ∗
    A 322 ↪[wf] FuncInst.wasm types[13]! inst f322 ∗ A 332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗
    A 333 ↪[wf] FuncInst.wasm types[0]! inst f333 ∗ A 339 ↪[wf] FuncInst.wasm types[11]! inst f339)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (endCode (GF := GF) n maxP inst mi A) := by
  unfold endCode; infer_instance

/-- The result of a punctuation check: 0 and the reader at `k` when accepted (`ok`), else a box. -/
def resEnd (ok : Prop) [Decidable ok] (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat) (de ptr : UInt32)
    (bs : List UInt8) (k j : Nat) (rs : List Value) : IProp GF :=
  if ok then iprop(⌜rs = [.i32 0]⌝ ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs k)
  else iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗ rd n de ptr bs j)

end Code

/-- The cost of a check: `K` and the whitespace, then an error unless accepted. -/
def costEnd (cfg : WasmConfig) (F K w j : Nat) (ok : Prop) [Decidable ok] : Nat :=
  (K + 96 * w) * cfg.regularOpCost + if ok then 0 else costErr cfg F (j + 1) + 20 * cfg.regularOpCost

theorem optByte_eqz (b : UInt8) : Numeric.bool (optByte (some b) &&& 256 == 0) = 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option hygiene false in
/-- Store the error code `k` in the frame at `sp - 16` (local 1), as the first word of the 12-byte
`ErrorCode` `C` that 322 reads. -/
local macro "store_code " k:term : tactic => `(tactic| (
  iunfold stk at F16
  icases F16 with ⟨%b16, %hb16, F16⟩
  icases U128From.memBytes_split n (sp - 16).toNat 4 b16 (by omega) $$ F16 with ⟨B0, B4⟩
  mstep; mstep
  mstep [B0] with (simp; omega)
  ihave C := U128From.memBytes_split n ((sp - 16).toNat + 4) 8 (b16.drop 4) (by simp; omega) $$ B4
  icases C with ⟨B4, B12⟩
  ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 $k) ((b16.drop 4).take 8) (by simp) $$ [B0 B4]
  · iframe B0 B4))

set_option hygiene false in
/-- From `call 322` (with the code `k` stored) to the function's end: the box, the frame put back, the
result `resEnd` on its rejecting side (`hno`). -/
local macro "err_call " k:term:max : tactic => `(tactic| (
  ihave S80 := stk_addr (show sp.toNat - 96 = (sp - 16).toNat - 80 by omega) $$ S80
  have key := SerdeErrBox.f322_spec (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 16) de (sp - 16) ptr idx (bytes32 $k ++ (b16.drop 4).take 8) bs j maxP mlen live F
    (by simp; omega) (by omega) (by omega) hjl (by omega) (by omega) (by omega) hr
  generalize costErr cfg F (j + 1) = E at key hX
  subst hX
  mcall key using [Hg S80 Hvt Hh C Hrd]
  · iframe Hg S80 Hvt Hh C Hrd
  clear key
  mcredits (20 * cfg.regularOpCost + R)
  icases HQ with ⟨%p, %⟨hrs, hp⟩, Hg, S80, Hvt, HA, C, Hrd⟩
  subst hrs
  mstep))

set_option hygiene false in
/-- After the error's `local.set`: out of the function, the frame put back, `resEnd` rejecting. -/
local macro "err_end " k:term:max hno:term : tactic => `(tactic| (
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  isplitl [S80 C B12]
  · ihave C := stk_intro n _ _ $$ C
    rw [show (bytes32 $k ++ (b16.drop 4).take 8).length = 12 by simp; omega]
    ihave B12 := stk_intro n _ _ $$ B12
    rw [show ((b16.drop 4).drop 8).length = 4 by simp; omega]
    ihave F16 := stk_join n (sp - 16).toNat 12 4 $$ [C B12]
    · rw [show (sp - 16).toNat + 12 = (sp - 16).toNat + 4 + 8 by omega]; iframe C B12
    ihave S80 := stk_addr (show (sp - 16).toNat - 80 = sp.toNat - 96 by omega) $$ S80
    ihave F16 := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ F16
    iapply stk_join n (sp.toNat - 96) 80 16
    iframe S80 F16
  iunfold resEnd
  rw [if_neg $hno]
  iexists p
  isplitr
  · ipureintro; simp [htype, hp]
  iframe HA Hrd))

section L320

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`end`** (320): only whitespace left. -/
theorem f320_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hsp : 96 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20) :
    endCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f320 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i))
        (fun _ => costEnd cfg F 200 (wsLen (bs.drop i)) (i + wsLen (bs.drop i))
          (i + wsLen (bs.drop i) = bs.length))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          resEnd (i + wsLen (bs.drop i) = bs.length) n maxP mlen live F de ptr bs bs.length
            (i + wsLen (bs.drop i)) rs)) := by
  iintro #Hv
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, #F640, #F322, #F332, #F333, #F339⟩
  ihave #Hcode' := Hcode
  iunfold errCode at Hcode'
  icases Hcode' with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha322 := hm.funcs 322 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Hrd⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  simp only [f320, costEnd]
  generalize hw : wsLen (bs.drop i) = w
  generalize hj : i + w = j
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  generalize hX : (if j = bs.length then 0 else costErr cfg F (j + 1) + 20 * cfg.regularOpCost) = X
  rw [show (200 + 96 * w) * cfg.regularOpCost + X + R =
    100 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + (X + R)) by simp only [Nat.add_mul]; omega]
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, hj, hW] at key
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (70 * cfg.regularOpCost + (X + R))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  icases stk_split n (sp.toNat - 96) 80 16 $$ Hs with ⟨S80, F16⟩
  rw [show sp.toNat - 96 + 80 = (sp - 16).toNat by omega]
  by_cases hje : j = bs.length
  · -- the end of the input: 0
    rw [if_pos hje] at hX
    subst hX
    have hnone : bs[j]? = none := List.getElem?_eq_none (by omega)
    rw [hnone]
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with decide
    (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
    mstep; mstep; mstep; mstep [Hg]
    rw [show sp - 16 + 16 = sp by simp]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hg Hvt
    isplitl [S80 F16]
    · ihave F16 := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ F16
      iapply stk_join n (sp.toNat - 96) 80 16
      iframe S80 F16
    iunfold resEnd
    rw [if_pos hje]
    isplitr
    · ipureintro; simp [htype]
    iframe Hh
    rw [← hje]
    iexact Hrd
  · -- a byte: `TrailingCharacters` (322)
    rw [if_neg hje] at hX
    obtain ⟨b, hb⟩ : ∃ b, bs[j]? = some b := ⟨bs[j]'(by omega), List.getElem?_eq_getElem _⟩
    rw [hb]
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with exact optByte_eqz b
    store_code 19
    mstep; mstep
    err_call 19
    err_end 19 hje

set_option hygiene false in
/-- The prologue of a check: the frame, `parse_whitespace` (339), its `Ok`. Leaves the reader at `j`,
the credits `40·c + X + R` with `X` the error's cost, and the stack split at `sp - 16`. -/
local macro "end_head " K:term:max ok:term : tactic => `(tactic| (
  iintro #Hv
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, #F640, #F322, #F332, #F333, #F339⟩
  ihave #Hcode' := Hcode
  iunfold errCode at Hcode'
  icases Hcode' with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha322 := hm.funcs 322 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Hrd⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  simp only [costEnd]
  generalize hw : wsLen (bs.drop i) = w
  generalize hj : i + w = j
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  generalize hX : (if $ok then 0 else costErr cfg F (j + 1) + 20 * cfg.regularOpCost) = X
  rw [show ($K + 96 * w) * cfg.regularOpCost + X + R =
    ($K - 100) * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + (X + R)) by
      simp only [Nat.add_mul, Nat.sub_mul]; omega]
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, hj, hW] at key
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (($K - 130) * cfg.regularOpCost + (X + R))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  icases stk_split n (sp.toNat - 96) 80 16 $$ Hs with ⟨S80, F16⟩
  rw [show sp.toNat - 96 + 80 = (sp - 16).toNat by omega]))

set_option hygiene false in
/-- The accepted byte eaten (333). -/
local macro "eat_ok" : tactic => `(tactic| (
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j (by omega) (by omega)
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs))

set_option hygiene false in
/-- The accepting end, after the result 0 is set: out of the function. -/
local macro "ok_tail " hok:term : tactic => `(tactic| (
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  isplitl [S80 F16]
  · ihave F16 := stk_addr (show (sp - 16).toNat = sp.toNat - 96 + 80 by omega) $$ F16
    iapply stk_join n (sp.toNat - 96) 80 16
    iframe S80 F16
  iunfold resEnd
  rw [if_pos $hok]
  isplitr
  · ipureintro; simp [htype]
  iframe Hh Hrd))

theorem some_bit (b : UInt8) : Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 256) 0) ≠ 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The byte tests `(r & 0xFF0000) != k << 16` of a peeked `Some b`, for `:`, `}`, `,`, `]`, `"`. -/
theorem byte_is58 (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 16711680) 3801088) = if b = 58 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem byte_is125 (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 16711680) 8192000) = if b = 125 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem byte_is44 (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 16711680) 2883584) = if b = 44 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem byte_is93 (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 16711680) 6094848) = if b = 93 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem byte_is34 (b : UInt8) :
    Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 16711680) 2228224) = if b = 34 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`parse_object_colon`** (89): whitespace, then `:`. -/
theorem f89_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hsp : 96 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20) :
    endCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f89 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i))
        (fun _ => costEnd cfg F 200 (wsLen (bs.drop i)) (i + wsLen (bs.drop i))
          (bs[i + wsLen (bs.drop i)]? = some 0x3A))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          resEnd (bs[i + wsLen (bs.drop i)]? = some 0x3A) n maxP mlen live F de ptr bs
            (i + wsLen (bs.drop i) + 1) (i + wsLen (bs.drop i)) rs)) := by
  simp only [f89]
  end_head 200 (bs[j]? = some 0x3A)
  rcases hbj : bs[j]? with _ | b
  · -- the end of the input: `EofWhileParsingObject` (3)
    have hno : ¬ (bs[j]? = some 0x3A) := by rw [hbj]; simp
    rw [if_neg hno] at hX
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with decide
    store_code 3
    mstep
    mstep; mstep
    err_call 3
    err_end 3 (by simp : ¬ ((none : Option UInt8) = some 0x3A))
  · by_cases hb : b = 0x3A
    · subst hb
      rw [if_pos hbj] at hX
      subst hX
      mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with decide
      have hjlt : j < bs.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hbj; simp at hbj
      eat_ok
      mstep; mstep; mstep
      ok_tail trivial
    · have hno : ¬ (bs[j]? = some 0x3A) := by rw [hbj]; simpa using hb
      rw [if_neg hno] at hX
      generalize hob : optByte (some b) = ob
      mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with (rw [← hob]; exact some_bit b)
      mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with (rw [← hob, byte_is58 b]; simp [hb])
      store_code 6
      mstep; mstep
      err_call 6
      err_end 6 (by simpa using hb)

theorem eq_is125 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 125) = if b = 125 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem ne_is44 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ne b.toUInt32 44) = if b = 44 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`end_map`** (90): whitespace, then `}`. -/
theorem f90_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hsp : 96 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20) :
    endCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f90 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i))
        (fun _ => costEnd cfg F 200 (wsLen (bs.drop i)) (i + wsLen (bs.drop i))
          (bs[i + wsLen (bs.drop i)]? = some 0x7D))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          resEnd (bs[i + wsLen (bs.drop i)]? = some 0x7D) n maxP mlen live F de ptr bs
            (i + wsLen (bs.drop i) + 1) (i + wsLen (bs.drop i)) rs)) := by
  simp only [f90]
  end_head 200 (bs[j]? = some 0x7D)
  rcases hbj : bs[j]? with _ | b
  · -- the end of the input: `EofWhileParsingObject` (3)
    have hno : ¬ (bs[j]? = some 0x7D) := by rw [hbj]; simp
    rw [if_neg hno] at hX
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with decide
    store_code 3
    mstep
    mstep; mstep
    err_call 3
    mstep
    err_end 3 (by simp : ¬ ((none : Option UInt8) = some 0x7D))
  · have hjlt : j < bs.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hbj; simp at hbj
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with exact some_bit b
    mstep; mstep; mstep; mstep; mstep; mstep
    rw [SerdeRead.optByte_byte b]
    mstep; mstep; mstep
    by_cases hb : b = 0x7D
    · subst hb
      rw [if_pos hbj] at hX
      subst hX
      mstep_taken with decide
      eat_ok
      mstep; mstep
      ok_tail trivial
    · have hno : ¬ (bs[j]? = some 0x7D) := by rw [hbj]; simpa using hb
      rw [if_neg hno] at hX
      mstep_not_taken with (rw [eq_is125, if_neg hb])
      by_cases hc : b = 0x2C
      · subst hc
        mstep; mstep; mstep; mstep
        mstep_not_taken with decide
        store_code 18
        mstep
        mstep; mstep
        err_call 18
        mstep
        err_end 18 (by decide : ¬ ((some (0x2C : UInt8)) = some 0x7D))
      · mstep; mstep; mstep; mstep
        mstep_taken with (rw [ne_is44, if_neg hc]; decide)
        store_code 19
        mstep; mstep
        err_call 19
        mstep
        err_end 19 (by simpa using hb)

end L320

end WNear.Binary.SerdeEnds
