import Bridge.Functions.ParseStrErr
import Bridge.Functions.SerdeErrRet
import Bridge.Functions.SerdeString

/-!
# serde_json's `deserialize_str` (380) into a `String` (M6)

```wat
;; 380 deserialize_str(out, de)     a 48-byte frame
peek := parse_whitespace(de)        ;; 339
None      → out := Err(peek_error(EofWhileParsingValue)) (322, code 5)
Some '"'  → eat_char (333); scratch.clear() (343 → 674);
            r := parse_str(de, scratch) (646); Err(e) → out := Err(e)
            Ok(s) → out := visit_str(s) (633): Ok(String)
Some _    → peek_invalid_type (340), fix_position (327)       ;; not covered here
```

* `f674_s`, `f343_s`: `Vec::truncate(0)` / `clear` on the scratch: its length becomes 0.
* `f380_s`: from the reader's index `i`, after the whitespace (`j = i + wsLen (bs.drop i)`), the
  input ends or holds `"`, then an escape-free string body (`ParseStrErr`'s `body ++ tail`). The
  result `res380`: `Ok(String)` holding `body` in a fresh block (`heapS`) when 646 accepts
  (`ok646`), else `Err(box)`. The case of another byte (340) is excluded by a hypothesis.
-/

namespace WNear.Binary.SerdeDeStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeString (heapS strCode cost618 costA)
open WNear.Binary.ParseStr (escTable plain ok646 cost646 res646)
open WNear.Binary.FromUtf8Gen (utf8Width)

section L674

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`Vec::truncate(v, 0)`** (674): the length becomes 0. -/
theorem f674_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (v x : UInt32) (hv : v.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f674 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 0]⌝ ∗ n ↦[i32][ v.toNat + 8 ] x))
        (fun _ => 12 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat + 8 ] 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, H8⟩
  subst hargs
  have h0 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u x 0) = 0 := by
    simp [Numeric.bool, Numeric.irelop32]
  simp only [f674]
  mstep; mstep; mstep [H8]; mstep; mstep
  mstep_not_taken with exact h0
  mstep; mstep; mstep [H8]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe H8

/-- **`Vec::clear(v)`** (343): 674 with 0. -/
theorem f343_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (v x : UInt32)
    (hv : v.toNat + 12 ≤ 2 ^ 32) :
    A 674 ↪[wf] FuncInst.wasm types[14]! inst f674 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f343 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat + 8 ] x))
        (fun _ => 30 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat + 8 ] 0)) := by
  iintro ⟨#F674, #Hi⟩
  have hn := hm.mem
  have ha := hm.funcs 674 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, H8⟩
  subst hargs
  simp only [f343]
  mstep; mstep
  mcall (f674_s cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg v x hv) using [H8]
  · iframe H8
  icases HQ with ⟨%hrs, H8⟩
  subst hrs
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe H8
  ipureintro; simp [htype]

end L674


set_option maxRecDepth 100000 in
theorem optByte_quote (b : UInt8) :
    Numeric.bool (optByte (some b) &&& 16711680 == 2228224) = if b = 0x22 then 1 else 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem optByte_none_some : Numeric.bool (Numeric.bool (optByte none &&& 256 == 0) == 0) = 0 := by decide

instance {GF : BundledGFunctors} [WasmGS NearState GF] (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (errCode (GF := GF) n maxP inst mi A) := by
  unfold errCode; infer_instance

section L380

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `deserialize_str` runs (persistent). -/
def code380 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(errCode n maxP inst mi A ∗ strCode n maxP inst mi A ∗
    A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗ A 657 ↪[wf] FuncInst.wasm types[31]! inst f657 ∗
    A 647 ↪[wf] FuncInst.wasm types[31]! inst f647 ∗ A 648 ↪[wf] FuncInst.wasm types[45]! inst f648 ∗
    A 646 ↪[wf] FuncInst.wasm types[31]! inst f646 ∗ A 640 ↪[wf] FuncInst.wasm types[14]! inst f640 ∗
    A 322 ↪[wf] FuncInst.wasm types[13]! inst f322 ∗ A 332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗
    A 333 ↪[wf] FuncInst.wasm types[0]! inst f333 ∗ A 339 ↪[wf] FuncInst.wasm types[11]! inst f339 ∗
    A 674 ↪[wf] FuncInst.wasm types[14]! inst f674 ∗ A 343 ↪[wf] FuncInst.wasm types[0]! inst f343 ∗
    A 633 ↪[wf] FuncInst.wasm types[31]! inst f633)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (code380 (GF := GF) n maxP inst mi A) := by
  unfold code380; infer_instance

/-- 380 accepts: a string at `j`, which 646 accepts. -/
def ok380 (bs body tail : List UInt8) (j : Nat) : Prop := j < bs.length ∧ ok646 body tail

instance (bs body tail : List UInt8) (j : Nat) : Decidable (ok380 bs body tail j) := by
  unfold ok380; infer_instance

/-- 380's result: `Ok(String)` holding `body` in a fresh block, or `Err(box)`. -/
def res380 (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat) (out de ptr : UInt32)
    (ob bs body tail : List UInt8) (j : Nat) : IProp GF :=
  if ok380 bs body tail j then
    iprop(∃ p : UInt32, n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
      n ↦[i32][ out.toNat + 8 ] UInt32.ofNat body.length ∗ n ↦[i32][ out.toNat + 12 ] UInt32.ofNat body.length ∗
      heapS n maxP mlen live F (UInt32.ofNat body.length) p ∗ n ↦[wms][ p.toNat ] body ∗
      rd n de ptr bs (j + 1 + body.length + 1))
  else
    iprop(∃ p : UInt32, ⌜p ≠ 0⌝ ∗ heapA n maxP mlen live F 20 p ∗ n ↦[i32][ out.toNat ] 1 ∗
      n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[wms][ out.toNat + 8 ] (ob.drop 8) ∗ ∃ k, rd n de ptr bs k)

end L380

/-- 380's cost: the whitespace, then the string (646), then `visit_str` (633) or an error. -/
def cost380 (cfg : WasmConfig) (F : Nat) (bs body tail : List UInt8) (j w : Nat) : Nat :=
  (350 + 96 * w) * cfg.regularOpCost + (if j < bs.length then cost646 cfg F (j + 1) body tail else 0) +
    if ok380 bs body tail j then 60 * cfg.regularOpCost + cost618 cfg F (UInt32.ofNat body.length)
    else costErr cfg F (j + 1) + 20 * cfg.regularOpCost

section L380

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`deserialize_str(out, de)`** (380) into a `String`: from the reader's index `i`, the whitespace,
then the end of the input or a `"` and an escape-free string body (`body ++ tail`, as
`ParseStrErr.f646_spec_noesc`). The result is `res380`. Another byte after the whitespace (the
`peek_invalid_type` path, 340) is excluded by `hq`. -/
theorem f380_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx sl : UInt32) (ob bs body tail : List UInt8) (i j : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 208 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i))
    (hq : j < bs.length → bs[j]? = some 0x22)
    (hsplit : bs.drop (j + 1) = body ++ tail) (hplain : ∀ b ∈ body, plain b = true)
    (hstop : ∀ x rest, tail = x :: rest → plain x = false ∧ x ≠ 0x5C)
    (hr : roomFor4 mlen maxP 20) (hrs : 0 < body.length → roomFor mlen maxP (UInt32.ofNat body.length)) :
    code380 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f380 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 208) 208 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width))
        (fun _ => cost380 cfg F bs body tail j (wsLen (bs.drop i)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 208) 208 ∗
          vt n 1057464 idx ta (A 578) ∗ (∃ sl', n ↦[i32][ de.toNat + 20 ] sl') ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          res380 n maxP mlen live F out de ptr ob bs body tail j)) := by
  iintro #Hv
  ihave #Hv' := Hv
  iunfold code380 at Hv'
  icases Hv' with ⟨#Hcode, #Hstr, #F927, #F657, #F647, #F648, #F646, #F640, #F322, #F332, #F333, #F339, #F674,
    #F343, #F633⟩
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
  have ha343 := hm.funcs 343 (by decide)
  have ha646 := hm.funcs 646 (by decide)
  have ha633 := hm.funcs 633 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hsl, He, Hw⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  simp only [f380, cost380]
  generalize hw : wsLen (bs.drop i) = w at hj
  generalize hX1 : (if j < bs.length then cost646 cfg F (j + 1) body tail else 0) = X1
  generalize hX2 : (if ok380 bs body tail j then 60 * cfg.regularOpCost + cost618 cfg F (UInt32.ofNat body.length)
    else costErr cfg F (j + 1) + 20 * cfg.regularOpCost) = X2
  rw [show (350 + 96 * w) * cfg.regularOpCost + X1 + X2 + R =
    250 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + (X1 + (X2 + R))) by simp only [Nat.add_mul]; omega]
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, ← hj, hW] at key
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (230 * cfg.regularOpCost + (X1 + (X2 + R)))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep; mstep
  icases stk_split n (sp.toNat - 208) 160 48 $$ Hs with ⟨S160, S48⟩
  rw [show sp.toNat - 208 + 160 = (sp - 48).toNat by omega]
  icases stk_split n (sp - 48).toNat 8 40 $$ S48 with ⟨F0, S40⟩
  icases stk_split n ((sp - 48).toNat + 8) 16 24 $$ S40 with ⟨A16, S24⟩
  icases stk_split n ((sp - 48).toNat + 8 + 16) 16 8 $$ S24 with ⟨B16, F8⟩
  have hB : (sp - 48 + 24).toNat = (sp - 48).toNat + 8 + 16 := by rw [UInt32.toNat_add, h48]; simp; omega
  have hA : (sp - 48 + 8).toNat = (sp - 48).toNat + 8 := by rw [UInt32.toNat_add, h48]; simp; omega
  by_cases hjl' : j < bs.length
  · -- a `"`: the string (646), then `visit_str` (633)
    rw [if_pos hjl'] at hX1
    subst hX1
    have hqq := hq hjl'
    rw [hqq]
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with decide
    mstep; mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j hjl' (by omega)
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    have hde12 : (de + 12).toNat = de.toNat + 12 := by rw [UInt32.toNat_add]; simp; omega
    ihave Hsl : n ↦[i32][ (de + 12).toNat + 8 ] sl $$ [Hsl]
    · rw [hde12, show de.toNat + 12 + 8 = de.toNat + 20 by omega]; iexact Hsl
    mstep; mstep; mstep; mstep
    mcall (f343_s cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg (de + 12) sl (by omega))
      using [Hsl]
    · iframe Hsl
    icases HQ with ⟨%hrs, Hsl⟩
    subst hrs
    mcredits (140 * cfg.regularOpCost + (cost646 cfg F (j + 1) body tail + (X2 + R)))
    iunfold stk at B16
    icases B16 with ⟨%b16, %hb16, B16⟩
    ihave B16 := memBytes_addr (show (sp - 48).toNat + 8 + 16 = (sp - 48 + 24).toNat by omega) $$ B16
    ihave S160 := stk_addr (show sp.toNat - 208 = (sp - 48).toNat - 160 by omega) $$ S160
    mstep; mstep; mstep; mstep; mstep
    have key := ParseStr.f646_spec_noesc (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega)
      Cg gt (sp - 48) (sp - 48 + 24) de (de + 12) ptr idx b16 bs body tail (j + 1) maxP mlen live F hb16 (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hsplit hplain hstop hr
    mcall key using [Hg S160 Hvt Hh B16 Hrd Hsl He Hw]
    · iframe Hg S160 Hvt Hh B16 Hrd Hsl He Hw
    clear key
    mcredits (100 * cfg.regularOpCost + (X2 + R))
    icases HQ with ⟨%hrs, Hg, S160, Hvt, Hsl, He, Hw, H646⟩
    subst hrs
    ihave Hsl : n ↦[i32][ de.toNat + 20 ] 0 $$ [Hsl]
    · rw [hde12, show de.toNat + 12 + 8 = de.toNat + 20 by omega]; iexact Hsl
    have h24 : (sp - 48 + 24).toNat = (sp - 48).toNat + 24 := by rw [UInt32.toNat_add, h48]; simp; omega
    by_cases hok : ok646 body tail
    · -- 646 accepts: `visit_str`
      have h380 : ok380 bs body tail j := ⟨hjl', hok⟩
      rw [if_pos h380] at hX2
      iunfold res646 at H646
      rw [if_pos hok]
      icases H646 with ⟨Hh, Q0, Q4, Q8, Q12, Hrd⟩
      rw [h24]
      have hm28 : body.length < 2 ^ 28 := by
        have := congrArg List.length hsplit; simp at this; omega
      have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
      have hmj : j + 1 + body.length ≤ bs.length := by
        have := congrArg List.length hsplit; simp at this; omega
      mstep; mstep [Q4] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep; mstep [Q0] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep_taken with decide
      mstep; mstep; mstep; mstep; mstep
      mstep [Q12] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep; mstep; mstep
      mstep [Q8] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep; mstep; mstep; mstep
      mstep_taken with decide
      -- the body's bytes, for the copy
      iunfold rd, sliceRead at Hrd
      icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
      icases U128From.memBytes_split n ptr.toNat (j + 1) bs (by omega) $$ Hb with ⟨B0, Bd⟩
      rw [hsplit]
      icases U128From.memBytes_split n (ptr.toNat + (j + 1)) body.length (body ++ tail) (by simp) $$ Bd with
        ⟨Bbody, Btail⟩
      rw [List.take_left' rfl, List.drop_left' rfl]
      ihave Bbody := memBytes_addr (show ptr.toNat + (j + 1) = (ptr + UInt32.ofNat (j + 1)).toNat by
        simp [UInt32.toNat_add]; omega) $$ Bbody
      iunfold stk at A16
      icases A16 with ⟨%a16, %ha16, A16⟩
      ihave A16 := memBytes_addr (show (sp - 48).toNat + 8 = (sp - 48 + 8).toNat by omega) $$ A16
      icases stk_split n ((sp - 48).toNat - 160) 64 96 $$ S160 with ⟨S64, S96⟩
      ihave S96 := stk_addr (show (sp - 48).toNat - 160 + 64 = (sp - 48).toNat - 96 by omega) $$ S96
      mstep; mstep; mstep; mstep; mstep
      have key := SerdeString.f633_s (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
        (sp - 48) (sp - 48 + 8) (ptr + UInt32.ofNat (j + 1)) (UInt32.ofNat body.length) idx maxP mlen live F a16 body
        ha16 (by omega) (by omega) hm32.symm (by simp [UInt32.toNat_add]; omega) (by omega) (by rw [hm32]; exact hrs)
      rw [hX2] at key
      mcall key using [Hg S96 Hvt Hh A16 Bbody]
      · iframe Hg S96 Hvt Hh A16 Bbody
      clear key
      mcredits (40 * cfg.regularOpCost + R)
      icases HQ with ⟨%hrs, %p, Hg, S96, Hvt, P0, P4, P8, P12, HA, Hp, Bbody⟩
      subst hrs
      icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
      icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
      mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep_taken with decide
      ihave P48 := KeyGet.join64 n ((sp - 48 + 8).toNat + 4) p (UInt32.ofNat body.length) $$ [P4 P8]
      · rw [show (sp - 48 + 8).toNat + 4 + 4 = (sp - 48 + 8).toNat + 8 by omega]; iframe P4 P8
      mstep; mstep
      mstep [P48] with (simp [UInt32.toNat_add]; omega)
      rw [ofNat_decode_pair]
      mstep [O4]
      rw [storeBytes_pair64]
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep [P12] with (simp [UInt32.toNat_add]; omega)
      mstep [O12] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep; mstep; mstep [O0]
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
      iframe Hg Hvt He Hw
      isplitr [Hsl HA Hp O0 O4 O12 D0 D4 D8 B0 Bbody Btail]
      · ihave P0 := stk_word n _ _ $$ P0
        ihave P48 := stk_intro n _ _ $$ P48
        ihave P12 := stk_word n _ _ $$ P12
        rw [show (bytes32 p ++ bytes32 (UInt32.ofNat body.length)).length = 8 by simp]
        ihave A4 := stk_join n (sp - 48 + 8).toNat 4 8 $$ [P0 P48]
        · iframe P0 P48
        ihave A16 := stk_join n (sp - 48 + 8).toNat 12 4 $$ [A4 P12]
        · rw [show (sp - 48 + 8).toNat + 12 = (sp - 48 + 8).toNat + 12 by rfl]; iframe A4 P12
        ihave A16 := stk_addr (show (sp - 48 + 8).toNat = (sp - 48).toNat + 8 by omega) $$ A16
        ihave Q0 := stk_word n _ _ $$ Q0
        ihave Q4 := stk_word n _ _ $$ Q4
        ihave Q8 := stk_word n _ _ $$ Q8
        ihave Q12 := stk_word n _ _ $$ Q12
        ihave B16 := VecFromElem.stk16_join n ((sp - 48).toNat + 24) $$ [Q0 Q4 Q8 Q12]
        · iframe Q0 Q4 Q8 Q12
        ihave B16 := stk_addr (show (sp - 48).toNat + 24 = (sp - 48).toNat + 8 + 16 by omega) $$ B16
        ihave S24 := stk_join n ((sp - 48).toNat + 8 + 16) 16 8 $$ [B16 F8]
        · iframe B16 F8
        ihave S40 := stk_join n ((sp - 48).toNat + 8) 16 24 $$ [A16 S24]
        · iframe A16 S24
        ihave S48 := stk_join n (sp - 48).toNat 8 40 $$ [F0 S40]
        · iframe F0 S40
        ihave S96 := stk_addr (show (sp - 48).toNat - 96 = (sp - 48).toNat - 160 + 64 by omega) $$ S96
        ihave S160 := stk_join n ((sp - 48).toNat - 160) 64 96 $$ [S64 S96]
        · iframe S64 S96
        ihave S160 := stk_addr (show (sp - 48).toNat - 160 = sp.toNat - 208 by omega) $$ S160
        ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 208 + 160 by omega) $$ S48
        iapply stk_join n (sp.toNat - 208) 160 48
        iframe S160 S48
      isplitl [Hsl]
      · iexists 0; iexact Hsl
      iunfold res380
      rw [if_pos h380]
      iexists p
      ihave O4 := KeyGet.split64 n (out.toNat + 4) p (UInt32.ofNat body.length) $$ O4
      icases O4 with ⟨O4, O8⟩
      rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega, show out.toNat + 4 + 8 = out.toNat + 12 by omega]
      iframe O0 O4 O8 O12 HA Hp
      iunfold rd, sliceRead
      rw [show j + 1 + body.length + 1 = j + 1 + body.length + 1 by rfl]
      iframe D0 D4 D8
      ihave Bbody := memBytes_addr (show (ptr + UInt32.ofNat (j + 1)).toNat = ptr.toNat + (j + 1) by
        simp [UInt32.toNat_add]; omega) $$ Bbody
      ihave Bd := U128From.memBytes_join n (ptr.toNat + (j + 1)) body.length body tail rfl $$ [Bbody Btail]
      · iframe Bbody Btail
      rw [← hsplit]
      ihave Bb := U128From.memBytes_join n ptr.toNat (j + 1) (bs.take (j + 1)) (bs.drop (j + 1)) (by simp; omega) $$ [B0 Bd]
      · iframe B0 Bd
      rw [List.take_append_drop]
      iexact Bb
    · -- 646 fails: its error
      have hn380 : ¬ ok380 bs body tail j := fun h => hok h.2
      iunfold res646 at H646
      rw [if_neg hok]
      icases H646 with ⟨%p, %hp, HA, Q0, Q4, Q8, Hrd⟩
      rw [h24]
      icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
      icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
      mstep; mstep [Q4] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep; mstep [Q0] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep_not_taken with decide
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
      iframe Hg Hvt He Hw
      isplitr [Hsl HA O0 O4 O8 Hrd]
      · ihave Q0 := stk_word n _ _ $$ Q0
        ihave Q4 := stk_word n _ _ $$ Q4
        ihave Q8 := stk_intro n _ _ $$ Q8
        rw [show (b16.drop 8).length = 8 by simp; omega]
        ihave Q04 := stk_join n ((sp - 48).toNat + 24) 4 4 $$ [Q0 Q4]
        · iframe Q0 Q4
        ihave B16 := stk_join n ((sp - 48).toNat + 24) 8 8 $$ [Q04 Q8]
        · rw [show (sp - 48).toNat + 24 + 4 + 4 = (sp - 48).toNat + 24 + 8 by omega]; iframe Q04 Q8
        ihave B16 := stk_addr (show (sp - 48).toNat + 24 = (sp - 48).toNat + 8 + 16 by omega) $$ B16
        ihave S24 := stk_join n ((sp - 48).toNat + 8 + 16) 16 8 $$ [B16 F8]
        · iframe B16 F8
        ihave S40 := stk_join n ((sp - 48).toNat + 8) 16 24 $$ [A16 S24]
        · iframe A16 S24
        ihave S48 := stk_join n (sp - 48).toNat 8 40 $$ [F0 S40]
        · iframe F0 S40
        ihave S160 := stk_addr (show (sp - 48).toNat - 160 = sp.toNat - 208 by omega) $$ S160
        ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 208 + 160 by omega) $$ S48
        iapply stk_join n (sp.toNat - 208) 160 48
        iframe S160 S48
      isplitl [Hsl]
      · iexists 0; iexact Hsl
      iunfold res380
      rw [if_neg hn380]
      iexists p
      isplitr
      · ipureintro; exact hp
      rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop], show out.toNat + 4 + 4 = out.toNat + 8 by omega]
      iframe HA O0 O4 O8
      iexists _
      iexact Hrd
  · -- the end of the input: `EofWhileParsingValue` (322)
    have hje : j = bs.length := by omega
    have hnone : bs[j]? = none := List.getElem?_eq_none (by omega)
    have hn380 : ¬ ok380 bs body tail j := fun h => hjl' h.1
    rw [if_neg hjl'] at hX1
    rw [if_neg hn380] at hX2
    subst hX1
    rw [hnone]
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with decide
    iunfold stk at B16
    icases B16 with ⟨%b16, %hb16, B16⟩
    icases U128From.memBytes_split n ((sp - 48).toNat + 8 + 16) 4 b16 (by omega) $$ B16 with ⟨B0, B4⟩
    mstep; mstep
    mstep [B0] with (simp [UInt32.toNat_add]; omega)
    mstep; mstep; mstep; mstep
    ihave C := U128From.memBytes_split n ((sp - 48).toNat + 8 + 16 + 4) 8 (b16.drop 4) (by simp; omega) $$ B4
    icases C with ⟨B4, B12⟩
    ihave C := U128From.memBytes_join n ((sp - 48).toNat + 8 + 16) 4 (bytes32 5) ((b16.drop 4).take 8) (by simp) $$ [B0 B4]
    · iframe B0 B4
    ihave C := memBytes_addr (show (sp - 48).toNat + 8 + 16 = (sp - 48 + 24).toNat by omega) $$ C
    icases stk_split n (sp.toNat - 208) 80 80 $$ S160 with ⟨S80, S80'⟩
    ihave S80' := stk_addr (show sp.toNat - 208 + 80 = (sp - 48).toNat - 80 by omega) $$ S80'
    have key := SerdeErrBox.f322_spec (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
      (sp - 48) de (sp - 48 + 24) ptr idx (bytes32 5 ++ (b16.drop 4).take 8) bs j maxP mlen live F
      (by simp; omega) (by omega) (by omega) hjl (by omega) (by omega) (by omega) hr
    rw [hX2] at key
    mcall key using [Hg S80' Hvt Hh C Hrd]
    · iframe Hg S80' Hvt Hh C Hrd
    clear key
    mcredits (40 * cfg.regularOpCost + R)
    icases HQ with ⟨%p, %⟨hrs, hp⟩, Hg, S80', Hvt, HA, C, Hrd⟩
    subst hrs
    icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
    icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
    mstep; mstep; mstep; mstep [O0]
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
    iframe Hg Hvt He Hw
    isplitr [Hsl HA O0 O4 O8 Hrd]
    · ihave C := stk_intro n _ _ $$ C
      rw [show (bytes32 5 ++ (b16.drop 4).take 8).length = 12 by simp; omega]
      ihave C := stk_addr hB $$ C
      ihave B12 := stk_intro n _ _ $$ B12
      rw [show ((b16.drop 4).drop 8).length = 4 by simp; omega]
      ihave B16 := stk_join n ((sp - 48).toNat + 8 + 16) 12 4 $$ [C B12]
      · rw [show (sp - 48).toNat + 8 + 16 + 12 = (sp - 48).toNat + 8 + 16 + 4 + 8 by omega]; iframe C B12
      ihave S24 := stk_join n ((sp - 48).toNat + 8 + 16) 16 8 $$ [B16 F8]
      · iframe B16 F8
      ihave S40 := stk_join n ((sp - 48).toNat + 8) 16 24 $$ [A16 S24]
      · iframe A16 S24
      ihave S48 := stk_join n (sp - 48).toNat 8 40 $$ [F0 S40]
      · iframe F0 S40
      ihave S80' := stk_addr (show (sp - 48).toNat - 80 = sp.toNat - 208 + 80 by omega) $$ S80'
      ihave S160 := stk_join n (sp.toNat - 208) 80 80 $$ [S80 S80']
      · iframe S80 S80'
      ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 208 + 160 by omega) $$ S48
      iapply stk_join n (sp.toNat - 208) 160 48
      iframe S160 S48
    isplitl [Hsl]
    · iexists sl; iexact Hsl
    iunfold res380
    rw [if_neg hn380]
    iexists p
    isplitr
    · ipureintro; exact hp
    rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop], show out.toNat + 4 + 4 = out.toNat + 8 by omega]
    iframe HA O0 O4 O8
    iexists j
    iexact Hrd

end L380

end WNear.Binary.SerdeDeStr
