import Bridge.Functions.SerdeValueSeed

/-!
# serde_json's `end_seq` (91) (M6)

```wat
;; 91 end_seq(de)        a 32-byte frame
ws (339); None → EofWhileParsingList (2); ']' → eat, 0
','  → eat; ws (339, its result kept at sp + 8);
       ']' → TrailingComma (18); else TrailingCharacters (19)   ;; the drop (92) of an `Err` from
                                                               ;; 339 never runs: 339 is `Ok`
_    → TrailingCharacters (19)
```

`f91_spec`: on `]` after the whitespace, 0 and the reader past it; otherwise a box `p ≠ 0` and the
reader somewhere (`resSeq`). The cost is `(300 + 96·w + 96·w')·c` with `w'` the second whitespace
(after a `,`), plus `costErr cfg F (len + 1) + 20·c` on an error.
-/

namespace WNear.Binary.SerdeEndSeq

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit byte_is93 eq_is125 ne_is44)

theorem costErr_mono (cfg : WasmConfig) (F a b : Nat) (h : a ≤ b) : costErr cfg F a ≤ costErr cfg F b := by
  unfold costErr SerdePosition.cost638 SerdePosition.cost645
  have := Nat.mul_le_mul_right cfg.regularOpCost (show 80 + (40 + (200 + 50 * a)) ≤ 80 + (40 + (200 + 50 * b)) by omega)
  omega

theorem eq_is93 (b : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 93) = if b = 93 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem wrap_tag (b : UInt8) : (optByte (some b)).toUInt32 &&& 255 = 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem some_byte_bit (b : UInt8) : Numeric.bool (optByte (some b) &&& 65280 == 0) = 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 91's result: 0 and the reader past `]`, or a box and the reader somewhere. -/
def resSeq (ok : Prop) [Decidable ok] (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat) (de ptr : UInt32)
    (bs : List UInt8) (k : Nat) (rs : List Value) : IProp GF :=
  if ok then iprop(⌜rs = [.i32 0]⌝ ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs k)
  else iprop(∃ (p : UInt32) (k' : Nat), ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗
    rd n de ptr bs k')

end Defs

/-- 91's cost. -/
def cost91 (cfg : WasmConfig) (F : Nat) (bs : List UInt8) (i : Nat) : Nat :=
  let j := i + wsLen (bs.drop i)
  (400 + 96 * wsLen (bs.drop i) + (if bs[j]? = some 0x2C then 96 * wsLen (bs.drop (j + 1)) else 0)) *
      cfg.regularOpCost +
    if bs[j]? = some 0x5D then 0 else costErr cfg F (bs.length + 1) + 20 * cfg.regularOpCost

set_option hygiene false in
/-- Store the error code `k` at `sp - 16` (local 1 + 16). -/
local macro "store16 " k:term : tactic => `(tactic| (
  iunfold stk at F16
  icases F16 with ⟨%b16, %hb16, F16⟩
  icases U128From.memBytes_split n (sp - 16).toNat 4 b16 (by omega) $$ F16 with ⟨B0, B4⟩
  mstep; mstep
  mstep [B0] with (simp [UInt32.toNat_add]; omega)
  ihave C := U128From.memBytes_split n ((sp - 16).toNat + 4) 8 (b16.drop 4) (by simp; omega) $$ B4
  icases C with ⟨B4, B12⟩
  ihave C := U128From.memBytes_join n (sp - 16).toNat 4 (bytes32 $k) ((b16.drop 4).take 8) (by simp) $$ [B0 B4]
  · iframe B0 B4))

set_option hygiene false in
/-- `peek_error(de, sp - 16)` (322) at the reader position `jj`, then `local.set 0`. -/
local macro "err91 " k:term:max jj:term:max : tactic => `(tactic| (
  ihave S80 := stk_addr (show sp.toNat - 112 = (sp - 32).toNat - 80 by omega) $$ S80
  ihave C := memBytes_addr (show (sp - 16).toNat = (sp - 32 + 16).toNat by simp [UInt32.toNat_add]; omega) $$ C
  mstep; mstep; mstep; mstep
  have key := SerdeErrBox.f322_spec (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) de (sp - 32 + 16) ptr idx (bytes32 $k ++ (b16.drop 4).take 8) bs $jj maxP mlen live F
    (by simp; omega) (by simp [UInt32.toNat_add]; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hr
  have hle := costErr_mono cfg F ($jj + 1) (bs.length + 1) (by omega)
  generalize costErr cfg F ($jj + 1) = E1 at key hle
  generalize costErr cfg F (bs.length + 1) = E at hX hle
  subst hX
  mcall key using [Hg S80 Hvt Hh C Hrd]
  · iframe Hg S80 Hvt Hh C Hrd
  clear key
  icases HQ with ⟨%p, %⟨hrs, hp⟩, Hg, S80, Hvt, HA, C, Hrd⟩
  subst hrs
  mstep))

set_option hygiene false in
/-- Out of 91 after an error: the frame put back (`L` the lower 16 bytes), `resSeq` rejecting. -/
local macro "end91 " k:term:max hno:term : tactic => `(tactic| (
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt
  isplitl [S80 C B12 L16]
  · ihave C := memBytes_addr (show (sp - 32 + 16).toNat = (sp - 16).toNat by simp [UInt32.toNat_add]; omega) $$ C
    ihave C := stk_intro n _ _ $$ C
    rw [show (bytes32 $k ++ (b16.drop 4).take 8).length = 12 by simp; omega]
    ihave B12 := stk_intro n _ _ $$ B12
    rw [show ((b16.drop 4).drop 8).length = 4 by simp; omega]
    ihave F16 := stk_join n (sp - 16).toNat 12 4 $$ [C B12]
    · rw [show (sp - 16).toNat + 12 = (sp - 16).toNat + 4 + 8 by omega]; iframe C B12
    ihave F16 := stk_addr (show (sp - 16).toNat = (sp - 32).toNat + 16 by omega) $$ F16
    ihave F32 := stk_join n (sp - 32).toNat 16 16 $$ [L16 F16]
    · iframe L16 F16
    ihave S80 := stk_addr (show (sp - 32).toNat - 80 = sp.toNat - 112 by omega) $$ S80
    ihave F32 := stk_addr (show (sp - 32).toNat = sp.toNat - 112 + 80 by omega) $$ F32
    iapply stk_join n (sp.toNat - 112) 80 32
    iframe S80 F32
  iunfold resSeq
  rw [if_neg $hno]
  iexists p, _
  isplitr
  · ipureintro; simp [htype, hp]
  iframe HA Hrd))

section L91

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`end_seq`** (91): whitespace, then `]`. -/
theorem f91_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr idx : UInt32) (bs : List UInt8) (i : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hsp : 112 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20) :
    endCode n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f91 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          rd n de ptr bs i))
        (fun _ => cost91 cfg F bs i)
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          resSeq (bs[i + wsLen (bs.drop i)]? = some 0x5D) n maxP mlen live F de ptr bs
            (i + wsLen (bs.drop i) + 1) rs)) := by
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
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  simp only [f91, cost91]
  generalize hw : wsLen (bs.drop i) = w
  generalize hj : i + w = j
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  generalize hX : (if bs[j]? = some 0x5D then 0 else costErr cfg F (bs.length + 1) + 20 * cfg.regularOpCost) = X
  generalize hV : (if bs[j]? = some 0x2C then 96 * wsLen (bs.drop (j + 1)) else 0) = V
  rw [show (400 + 96 * w + V) * cfg.regularOpCost + X + R =
    300 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + (V * cfg.regularOpCost + X + R)) by
      simp only [Nat.add_mul]; omega]
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W
  generalize hVc : V * cfg.regularOpCost = Vc
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, hj, hW] at key
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (270 * cfg.regularOpCost + (Vc + X + R))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  icases stk_split n (sp.toNat - 112) 80 32 $$ Hs with ⟨S80, F32⟩
  rw [show sp.toNat - 112 + 80 = (sp - 32).toNat by omega]
  icases stk_split n (sp - 32).toNat 16 16 $$ F32 with ⟨L16, F16⟩
  rw [show (sp - 32).toNat + 16 = (sp - 16).toNat by omega]
  rcases hbj : bs[j]? with _ | b
  · -- the end of the input: `EofWhileParsingList` (2)
    have hno : ¬ (bs[j]? = some 0x5D) := by rw [hbj]; simp
    rw [if_neg hno] at hX
    have hV0 : V = 0 := by rw [← hV, if_neg (by rw [hbj]; simp)]
    subst hV0
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with decide
    store16 2
    err91 2 j
    mstep
    end91 2 (by simp : ¬ ((none : Option UInt8) = some 0x5D))
  · have hjlt : j < bs.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hbj; simp at hbj
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with exact some_bit b
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    rw [SerdeRead.optByte_byte b]
    mstep; mstep; mstep
    by_cases hb : b = 0x5D
    · subst hb
      rw [if_pos hbj] at hX
      subst hX
      have hV0 : V = 0 := by rw [← hV, if_neg (by rw [hbj]; decide)]
      subst hV0
      mstep_taken with decide
      mstep
      mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j hjlt (by omega)
        (by omega)) using [Hrd]
      · iframe Hrd
      icases HQ with ⟨%hrs, Hrd⟩
      subst hrs
      mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep; mstep [Hg]
      rw [show sp - 32 + 32 = sp by simp]
      repeat mstep
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe Hg Hvt
      isplitl [S80 L16 F16]
      · ihave F16 := stk_addr (show (sp - 16).toNat = (sp - 32).toNat + 16 by omega) $$ F16
        ihave F32 := stk_join n (sp - 32).toNat 16 16 $$ [L16 F16]
        · iframe L16 F16
        ihave F32 := stk_addr (show (sp - 32).toNat = sp.toNat - 112 + 80 by omega) $$ F32
        iapply stk_join n (sp.toNat - 112) 80 32
        iframe S80 F32
      iunfold resSeq
      rw [if_pos trivial]
      isplitr
      · ipureintro; simp [htype]
      iframe Hh Hrd
    · have hno : ¬ (bs[j]? = some 0x5D) := by rw [hbj]; simpa using hb
      rw [if_neg hno] at hX
      mstep_not_taken with (rw [eq_is93, if_neg hb])
      by_cases hc : b = 0x2C
      · subst hc
        have hV' : V = 96 * wsLen (bs.drop (j + 1)) := by rw [← hV, if_pos hbj]
        generalize hw2 : wsLen (bs.drop (j + 1)) = w2 at hV'
        subst hV'
        have hj2l : j + 1 + w2 ≤ bs.length := by
          have := SerdeRead.wsLen_le (bs.drop (j + 1)); simp at this; omega
        mstep; mstep; mstep; mstep
        mstep_not_taken with decide
        mstep
        mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j hjlt (by omega)
          (by omega)) using [Hrd]
        · iframe Hrd
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        mstep; mstep
        have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
          (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs (j + 1) (by omega) (by omega)
          (by omega) (by omega)
        rw [hw2] at key
        have hVc' : (100 + 96 * w2) * cfg.regularOpCost = 100 * cfg.regularOpCost + Vc := by
          rw [← hVc]; simp only [Nat.add_mul]
        rw [hVc'] at key
        mcall key using [Hrd]
        · iframe Hrd
        clear key
        mcredits (100 * cfg.regularOpCost + (X + R))
        icases HQ with ⟨%hrs, Hrd⟩
        subst hrs
        generalize hj2 : j + 1 + w2 = j2 at hj2l ⊢
        icases stk_split n (sp - 32).toNat 8 8 $$ L16 with ⟨L8, M8⟩
        iunfold stk at M8
        icases M8 with ⟨%m8, %hm8, M8⟩
        mstep
        mstep [M8] with (simp [UInt32.toNat_add]; omega)
        ihave M8 := stk_intro n _ _ $$ M8
        rw [show (storeBytes (Value.i64 (optByte bs[j2]?)) 8).length = 8 by simp [storeBytes]]
        ihave L16 := stk_join n (sp - 32).toNat 8 8 $$ [L8 M8]
        · iframe L8 M8
        mstep; mstep; mstep; mstep; mstep
        rcases hbj2 : bs[j2]? with _ | b2
        · mstep
          mstep_not_taken with decide
          mstep; mstep; mstep; mstep
          mstep_taken with decide
          store16 19
          err91 19 j2
          mstep; mstep
          mstep_taken with decide
          end91 19 (by decide : ¬ ((some (0x2C : UInt8)) = some 0x5D))
        · rw [wrap_tag b2]
          mstep
          mstep_not_taken with decide
          mstep; mstep; mstep; mstep
          mstep_not_taken with exact some_byte_bit b2
          mstep; mstep; mstep; mstep; mstep
          by_cases hb2 : b2 = 0x5D
          · subst hb2
            mstep_not_taken with decide
            store16 18
            err91 18 j2
            mstep
            end91 18 (by decide : ¬ ((some (0x2C : UInt8)) = some 0x5D))
          · mstep_taken with (rw [byte_is93, if_neg hb2]; decide)
            store16 19
            err91 19 j2
            mstep; mstep
            mstep_taken with decide
            end91 19 (by decide : ¬ ((some (0x2C : UInt8)) = some 0x5D))
      · have hV0 : V = 0 := by rw [← hV, if_neg (by rw [hbj]; simpa using hc)]
        subst hV0
        mstep; mstep; mstep; mstep
        mstep_taken with (rw [ne_is44, if_neg hc]; decide)
        store16 19
        err91 19 j
        mstep
        end91 19 (by simpa using hb)

end L91

end WNear.Binary.SerdeEndSeq
