import Bridge.Functions.SerdeErrBox

/-!
# serde_json's `Deserializer::error` and `peek_error` returning the box (M6)

The parser's other syntax errors go through two functions that return the `Box<ErrorImpl>` instead of
writing a `Result` (`SerdeErrBox` proved 647, which writes `Err(box)`):

```wat
;; 325 error(rd, code) → box       (line, col) := position(rd) (638); Error::syntax(*code, line, col)
;; 322 peek_error(rd, code) → box  (line, col) := peek_position(rd) (640); Error::syntax(...)
;; 640 peek_position(out, rd)      position_of_index(min(index + 1, len)) (645)
```

The specifications are loose, as the reject paths need: a fresh 20-byte box, at most `costErr cfg F i`
for 325 and `costErr cfg F (i + 1)` for 322.

* `f325_spec`: `error`, at the reader's index `i`.
* `f640_spec`: `peek_position`, `position_of_index` at `min (i + 1) len`, at most `cost638 (i + 1)`.
* `f322_spec`: `peek_error`.
-/

namespace WNear.Binary.SerdeErrBox

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)

section L325

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdePosition (cost638 cost645 f638_spec)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Deserializer::error(rd, code)`** (325): the position of the reader's index (638), then
`Error::syntax` (639) on the 12-byte `ErrorCode` at `c`: the box, a fresh 20-byte block. At most
`costErr cfg F i`. -/
theorem f325_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de c ptr idx : UInt32) (cb bs : List UInt8) (i : Nat) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hcb : cb.length = 12) (hc : c.toNat + 12 ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 80 ≤ sp.toNat)
    (hr : roomFor4 len maxP 20) :
    errCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f325 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ c.toNat ] cb ∗ rd n de ptr bs i))
        (fun _ => costErr cfg F i)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F 20 p ∗
          n ↦[wms][ c.toNat ] cb ∗ rd n de ptr bs i)) := by
  iintro Hcode
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #H583, #H609, #H645, #H638⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha638 := hm.funcs 638 (by decide)
  have ha639 := hm.funcs 639 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hcb, Hrd⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 80) 48 32 $$ Hs with ⟨S48, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48) 8 24 $$ Hs with ⟨S8, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48 + 8) 8 16 $$ Hs with ⟨SP, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48 + 8 + 8) 12 4 $$ Hs with ⟨SE, S4⟩
  iunfold stk at SP SE
  icases SP with ⟨%sp8, %hsp8, SP⟩
  icases SE with ⟨%se, %hse, SE⟩
  icases U128From.memBytes_split n c.toNat 8 cb (by omega) $$ Hcb with ⟨C0, C8⟩
  simp only [f325, costErr]
  generalize hK2 : AllocWalk.cost310W cfg F 20 4 = K2
  rw [show (80 + cost638 i) * cfg.regularOpCost + (150 * cfg.regularOpCost + K2) + R =
    230 * cfg.regularOpCost + (cost638 i * cfg.regularOpCost + (K2 + R)) by rw [Nat.add_mul]; omega]
  have h8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by rw [UInt32.toNat_add, h32]; simp; omega
  have key638 := f638_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg (A 583) (A 609) (A 645)
    (hm.funcs 583 (by decide)) (hm.funcs 609 (by decide)) (hm.funcs 645 (by decide)) (by omega) Cg gt (sp - 32)
    (sp - 32 + 8) de ptr sp8 bs i hsp8 (by omega) hde hi hlen hptr (by omega)
  ihave S48 := stk_addr (show sp.toNat - 80 = (sp - 32).toNat - 48 by omega) $$ S48
  ihave SP := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 = (sp - 32 + 8).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ SP
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  have hK3 : (12 + cost638 i) * cfg.regularOpCost = 12 * cfg.regularOpCost + cost638 i * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  have hK4 : (11 + cost638 i) * cfg.regularOpCost = 11 * cfg.regularOpCost + cost638 i * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  mcall key638 using [Hg S48 SP Hrd]
  · iframe Hg S48 SP Hrd
  rw [hK4]
  clear hK3 hK4
  generalize cost638 i * cfg.regularOpCost = K1
  mcredits (210 * cfg.regularOpCost + (K2 + R))
  clear key638
  icases HQ with ⟨%hrs, Hg, S48, ⟨%line, %col, L0, L4⟩, Hrd⟩
  subst hrs
  icases U128From.memBytes_split n (sp.toNat - 80 + 48 + 8 + 8) 8 se (by omega) $$ SE with ⟨SE0, SE8⟩
  ihave SE0 := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 + 8 = (sp - 32).toNat + 16 by omega) $$ SE0
  ihave SE8 := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 + 8 + 8 = (sp - 32 + 16 + 8).toNat by
    rw [UInt32.toNat_add, UInt32.toNat_add, h32]; simp; omega) $$ SE8
  mstep; mstep [L4] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep [L0] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep
  mstep [C8] with (simp [UInt32.toNat_add]; omega)
  mstep [SE8]
  mstep; mstep; mstep [C0]
  mstep [SE0]
  mstep; mstep; mstep; mstep; mstep
  ihave E := U128From.memBytes_join n ((sp - 32).toNat + 16) 8
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8)
    (bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes]) $$ [SE0 SE8]
  · rw [show (sp - 32).toNat + 16 + 8 = (sp - 32 + 16 + 8).toNat by rw [UInt32.toNat_add, UInt32.toNat_add, h32]; simp; omega]
    iframe SE0 SE8
  ihave E := AllocNewCell.memBytes_addr (show (sp - 32).toNat + 16 = (sp - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ E
  have key639 := f639_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) (sp - 32 + 16) line col idx maxP len live F
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes])
    (by rw [UInt32.toNat_add, h32]; simp; omega) (by omega) hr
  rw [hK2] at key639
  clear hK2
  ihave S48 := stk_addr (show (sp - 32).toNat - 48 = (sp - 32).toNat - 48 by rfl) $$ S48
  mcall key639 using [Hg S48 Hvt Hinv E]
  · iframe Hg S48 Hvt Hinv E
  mcredits (34 * cfg.regularOpCost + R)
  clear key639
  icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, S48, Hvt, HA, E⟩
  subst hrs
  mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p
  isplitr
  · ipureintro; exact ⟨by simp [htype], hp0⟩
  iframe Hg Hvt HA Hrd
  isplitr [C0 C8]
  · ihave L0 := stk_word n _ _ $$ L0
    ihave L4 := stk_word n _ _ $$ L4
    ihave Lw := stk_join n (sp - 32 + 8).toNat 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave Lw := stk_addr (show (sp - 32 + 8).toNat = sp.toNat - 80 + 48 + 8 by omega) $$ Lw
    ihave J1 := stk_join n (sp.toNat - 80 + 48) 8 8 $$ [S8 Lw]
    · iframe S8 Lw
    ihave E := stk_intro n _ _ $$ E
    ihave E := stk_addr (show (sp - 32 + 16).toNat = sp.toNat - 80 + 48 + 16 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ E
    rw [show (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))).length = 12 by simp [storeBytes]]
    ihave J2 := stk_join n (sp.toNat - 80 + 48) 16 12 $$ [J1 E]
    · iframe J1 E
    ihave S4 := stk_addr (show sp.toNat - 80 + 48 + 8 + 8 + 12 = sp.toNat - 80 + 48 + 28 by omega) $$ S4
    ihave J3 := stk_join n (sp.toNat - 80 + 48) 28 4 $$ [J2 S4]
    · iframe J2 S4
    ihave S48 := stk_addr (show (sp - 32).toNat - 48 = sp.toNat - 80 by omega) $$ S48
    iapply stk_join n (sp.toNat - 80) 48 32
    iframe S48 J3
  ihave C := U128From.memBytes_join n c.toNat 8 (cb.take 8) (cb.drop 8) (by simp; omega) $$ [C0 C8]
  · iframe C0 C8
  rw [List.take_append_drop]
  iexact C


end L325

end WNear.Binary.SerdeErrBox

namespace WNear.Binary.SerdeErrBox

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdePosition (cost638 cost645 f645_spec)

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- `select` on the stack `vs ++ [a, b, c]`: `a` when `c ≠ 0`, else `b`. -/
theorem mwpi_select_vs {vs : List Value} {t : Option (List ValType)} {a b : Value} {c : UInt32} :
    credits Cg K ∗ ⌜cfg.regularOpCost ≤ K⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal (vs ++ [if c = 0 then b else a]) f)
      ⊢ mwpi cfg lim d f (vs ++ [a, b, .i32 c]) [.select t] Φ := by
  iintro ⟨Hc, %hK, H⟩
  by_cases hc : c = 0
  · subst hc
    iapply mwpi_select_false (vs := vs) (Φ := Φ) (R := K - cfg.regularOpCost) t a b
    rw [Nat.add_sub_cancel' hK]
    iframe Hc
    simp only [if_pos]
    iexact H
  · iapply mwpi_select_true (vs := vs) (Φ := Φ) (R := K - cfg.regularOpCost) t a b c hc
    rw [Nat.add_sub_cancel' hK]
    iframe Hc
    simp only [hc, if_false]
    iexact H

/-- `select` under two values. -/
theorem mwpi_select2 {x y : Value} {t : Option (List ValType)} {a b : Value} {c : UInt32} :
    credits Cg K ∗ ⌜cfg.regularOpCost ≤ K⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal [x, y, if c = 0 then b else a] f)
      ⊢ mwpi cfg lim d f [x, y, a, b, .i32 c] [.select t] Φ :=
  mwpi_select_vs (vs := [x, y])

end Flex

section L640

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem cost645_mono (a b : Nat) (h : a ≤ b) (c : Nat) : cost645 a * c ≤ cost645 b * c :=
  Nat.mul_le_mul_right c (by unfold cost645; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`SliceRead::peek_position(out, rd)`** (640): `position_of_index` at `min (i + 1) len`, some
`(line, column)` at `out`, at most `20 + cost638 (i + 1)`. The stack: 48 bytes. -/
theorem f640_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a583 a609 a645 : Nat)
    (ha583 : mi.funcAddrs[583]? = some a583) (ha609 : mi.funcAddrs[609]? = some a609)
    (ha645 : mi.funcAddrs[645]? = some a645) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr : UInt32) (ob bs : List UInt8) (i : Nat) (hob : ob.length = 8)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 48 ≤ sp.toNat) :
    a583 ↪[wf] FuncInst.wasm types[36]! inst f583 ∗ a609 ↪[wf] FuncInst.wasm types[39]! inst f609 ∗
      a645 ↪[wf] FuncInst.wasm types[31]! inst f645 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f640 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i))
        (fun _ => (20 + cost638 (i + 1)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 48) 48 ∗
          (∃ line col : UInt32, n ↦[i32][ out.toNat ] line ∗ n ↦[i32][ out.toNat + 4 ] col) ∗
          rd n de ptr bs i)) := by
  iintro ⟨#F583, #F609, #F645, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, Hrd⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  icases stk_split n (sp.toNat - 48) 32 16 $$ Hs with ⟨S32, Hs⟩
  icases stk_split n (sp.toNat - 48 + 32) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat (i + 1))) = 0
      then Value.i32 (UInt32.ofNat bs.length) else Value.i32 (UInt32.ofNat (i + 1))) =
      Value.i32 (UInt32.ofNat (min (i + 1) bs.length)) := by
    by_cases hib : i + 1 < bs.length
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat (i + 1))) ≠ 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      rw [if_neg this, Nat.min_eq_left (by omega)]
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat (i + 1))) = 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      rw [if_pos this, Nat.min_eq_right (by omega)]
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (i + 1)) (UInt32.ofNat i)) = 0 := by
    rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
  generalize hj : min (i + 1) bs.length = j at hsel
  have hjl : j ≤ bs.length := by omega
  have hle := cost645_mono j (i + 1) (by omega) cfg.regularOpCost
  simp only [f640, cost638]
  rw [show (20 + (40 + cost645 (i + 1))) * cfg.regularOpCost + R =
    60 * cfg.regularOpCost + (cost645 j * cfg.regularOpCost + ((cost645 (i + 1) * cfg.regularOpCost - cost645 j * cfg.regularOpCost) + R)) by
    simp only [Nat.add_mul]; omega]
  generalize hR' : cost645 (i + 1) * cfg.regularOpCost - cost645 j * cfg.regularOpCost + R = R'
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [D8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep
  rw [SerdeRead.ofNat_succ i (by omega)]
  mstep; mstep; mstep
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro
  exact ⟨rfl, by omega, hov⟩
  inext; iintro Hc; mctrl_norm
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [D4] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply mwpi_select2
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; omega
  inext
  iintro Hc
  rw [hsel]
  clear hsel
  mctrl_norm
  have t31 : types[31]!.params.length = 3 := by rfl
  ihave S32 := VecFromElem.stk_addr (show sp.toNat - 48 = (sp - 16).toNat - 32 by omega) $$ S32
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 48 + 32 + 8 = (sp - 16 + 8).toNat by omega) $$ S8'
  have hK2 : (12 + cost645 (UInt32.ofNat j).toNat) * cfg.regularOpCost = 12 * cfg.regularOpCost + cost645 j * cfg.regularOpCost := by
    rw [show (UInt32.ofNat j).toNat = j by simp; omega, Nat.add_mul]
  have hK3 : (13 + cost645 j) * cfg.regularOpCost = 13 * cfg.regularOpCost + cost645 j * cfg.regularOpCost := Nat.add_mul _ _ _
  mcall (f645_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n g hn hg a583 a609 ha583 ha609 (by omega)
    Cg gt (sp - 16) (sp - 16 + 8) de ptr s8 bs j hs8 (by omega) (by omega) hjl hlen hptr (by omega))
    using [Hg S32 S8' D0 D4 Hb]
  · iframe Hg S32 S8' D0 D4 Hb
  try rw [hK3]
  try rw [hK2]
  generalize cost645 j * cfg.regularOpCost = K1
  mcredits (16 * cfg.regularOpCost + R')
  icases HQ with ⟨%hrs, Hg, S32, ⟨%line, %col, L0, L4⟩, D0, D4, Hb⟩
  subst hrs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  mstep; mstep; mstep [L0] with (simp [UInt32.toNat_add]; omega)
  mstep [O0]
  mstep; mstep; mstep [L4] with (simp [UInt32.toNat_add]; omega)
  mstep [O4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hg
  isplitl [S32 S8 L0 L4]
  · ihave L0 := stk_word n _ _ $$ L0
    ihave L4 := stk_word n _ _ $$ L4
    ihave L8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave L8 := VecFromElem.stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 48 + 32 + 8 by omega) $$ L8
    ihave S16 := stk_join n (sp.toNat - 48 + 32) 8 8 $$ [S8 L8]
    · iframe S8 L8
    ihave S32 := VecFromElem.stk_addr (show (sp - 16).toNat - 32 = sp.toNat - 48 by omega) $$ S32
    iapply stk_join n (sp.toNat - 48) 32 16
    iframe S32 S16
  isplitl [O0 O4]
  · iexists _, _
    iframe O0 O4
  iunfold rd, sliceRead
  iframe D0 D4 D8 Hb

end L640

end WNear.Binary.SerdeErrBox

namespace WNear.Binary.SerdeErrBox

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)

section L322

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdePosition (cost638 cost645)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Deserializer::peek_error(rd, code)`** (322): the position past the reader's index (640), then
`Error::syntax` (639) on the 12-byte `ErrorCode` at `c`: the box, a fresh 20-byte block. At most
`costErr cfg F (i + 1)` and 20 more. -/
theorem f322_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de c ptr idx : UInt32) (cb bs : List UInt8) (i : Nat) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hcb : cb.length = 12) (hc : c.toNat + 12 ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ bs.length)
    (hlen : bs.length + 1 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hsp : 80 ≤ sp.toNat)
    (hr : roomFor4 len maxP 20) :
    errCode n maxP inst mi A ∗ A 640 ↪[wf] FuncInst.wasm types[14]! inst f640
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f322 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ c.toNat ] cb ∗ rd n de ptr bs i))
        (fun _ => costErr cfg F (i + 1) + 20 * cfg.regularOpCost)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP len live F 20 p ∗
          n ↦[wms][ c.toNat ] cb ∗ rd n de ptr bs i)) := by
  iintro ⟨Hcode, #H640⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #H583, #H609, #H645, #H638⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha640 := hm.funcs 640 (by decide)
  have ha639 := hm.funcs 639 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hcb, Hrd⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 80) 48 32 $$ Hs with ⟨S48, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48) 8 24 $$ Hs with ⟨S8, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48 + 8) 8 16 $$ Hs with ⟨SP, Hs⟩
  icases stk_split n (sp.toNat - 80 + 48 + 8 + 8) 12 4 $$ Hs with ⟨SE, S4⟩
  iunfold stk at SP SE
  icases SP with ⟨%sp8, %hsp8, SP⟩
  icases SE with ⟨%se, %hse, SE⟩
  icases U128From.memBytes_split n c.toNat 8 cb (by omega) $$ Hcb with ⟨C0, C8⟩
  simp only [f322, costErr]
  generalize hK2 : AllocWalk.cost310W cfg F 20 4 = K2
  rw [show (80 + cost638 (i + 1)) * cfg.regularOpCost + (150 * cfg.regularOpCost + K2) + 20 * cfg.regularOpCost + R =
    230 * cfg.regularOpCost + ((20 + cost638 (i + 1)) * cfg.regularOpCost + (K2 + R)) by simp only [Nat.add_mul]; omega]
  have h8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by rw [UInt32.toNat_add, h32]; simp; omega
  have key638 := f640_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg (A 583) (A 609) (A 645)
    (hm.funcs 583 (by decide)) (hm.funcs 609 (by decide)) (hm.funcs 645 (by decide)) (by omega) Cg gt (sp - 32)
    (sp - 32 + 8) de ptr sp8 bs i hsp8 (by omega) hde hi hlen hptr (by omega)
  ihave S48 := stk_addr (show sp.toNat - 80 = (sp - 32).toNat - 48 by omega) $$ S48
  ihave SP := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 = (sp - 32 + 8).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ SP
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  have hK3 : (12 + (20 + cost638 (i + 1))) * cfg.regularOpCost = 12 * cfg.regularOpCost + (20 + cost638 (i + 1)) * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  have hK4 : (11 + (20 + cost638 (i + 1))) * cfg.regularOpCost = 11 * cfg.regularOpCost + (20 + cost638 (i + 1)) * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  mcall key638 using [Hg S48 SP Hrd]
  · iframe Hg S48 SP Hrd
  rw [hK3]
  clear hK3 hK4
  generalize (20 + cost638 (i + 1)) * cfg.regularOpCost = K1
  mcredits (205 * cfg.regularOpCost + (K2 + R))
  clear key638
  icases HQ with ⟨%hrs, Hg, S48, ⟨%line, %col, L0, L4⟩, Hrd⟩
  subst hrs
  icases U128From.memBytes_split n (sp.toNat - 80 + 48 + 8 + 8) 8 se (by omega) $$ SE with ⟨SE0, SE8⟩
  ihave SE0 := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 + 8 = (sp - 32).toNat + 16 by omega) $$ SE0
  ihave SE8 := AllocNewCell.memBytes_addr (show sp.toNat - 80 + 48 + 8 + 8 + 8 = (sp - 32 + 16 + 8).toNat by
    rw [UInt32.toNat_add, UInt32.toNat_add, h32]; simp; omega) $$ SE8
  mstep; mstep [L4] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep [L0] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep
  mstep [C8] with (simp [UInt32.toNat_add]; omega)
  mstep [SE8]
  mstep; mstep; mstep [C0]
  mstep [SE0]
  mstep; mstep; mstep; mstep; mstep
  ihave E := U128From.memBytes_join n ((sp - 32).toNat + 16) 8
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8)
    (bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes]) $$ [SE0 SE8]
  · rw [show (sp - 32).toNat + 16 + 8 = (sp - 32 + 16 + 8).toNat by rw [UInt32.toNat_add, UInt32.toNat_add, h32]; simp; omega]
    iframe SE0 SE8
  ihave E := AllocNewCell.memBytes_addr (show (sp - 32).toNat + 16 = (sp - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ E
  have key639 := f639_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) (sp - 32 + 16) line col idx maxP len live F
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes])
    (by rw [UInt32.toNat_add, h32]; simp; omega) (by omega) hr
  rw [hK2] at key639
  clear hK2
  ihave S48 := stk_addr (show (sp - 32).toNat - 48 = (sp - 32).toNat - 48 by rfl) $$ S48
  mcall key639 using [Hg S48 Hvt Hinv E]
  · iframe Hg S48 Hvt Hinv E
  mcredits (25 * cfg.regularOpCost + R)
  clear key639
  icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, S48, Hvt, HA, E⟩
  subst hrs
  mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p
  isplitr
  · ipureintro; exact ⟨by simp [htype], hp0⟩
  iframe Hg Hvt HA Hrd
  isplitr [C0 C8]
  · ihave L0 := stk_word n _ _ $$ L0
    ihave L4 := stk_word n _ _ $$ L4
    ihave Lw := stk_join n (sp - 32 + 8).toNat 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave Lw := stk_addr (show (sp - 32 + 8).toNat = sp.toNat - 80 + 48 + 8 by omega) $$ Lw
    ihave J1 := stk_join n (sp.toNat - 80 + 48) 8 8 $$ [S8 Lw]
    · iframe S8 Lw
    ihave E := stk_intro n _ _ $$ E
    ihave E := stk_addr (show (sp - 32 + 16).toNat = sp.toNat - 80 + 48 + 16 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ E
    rw [show (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))).length = 12 by simp [storeBytes]]
    ihave J2 := stk_join n (sp.toNat - 80 + 48) 16 12 $$ [J1 E]
    · iframe J1 E
    ihave S4 := stk_addr (show sp.toNat - 80 + 48 + 8 + 8 + 12 = sp.toNat - 80 + 48 + 28 by omega) $$ S4
    ihave J3 := stk_join n (sp.toNat - 80 + 48) 28 4 $$ [J2 S4]
    · iframe J2 S4
    ihave S48 := stk_addr (show (sp - 32).toNat - 48 = sp.toNat - 80 by omega) $$ S48
    iapply stk_join n (sp.toNat - 80) 48 32
    iframe S48 J3
  ihave C := U128From.memBytes_join n c.toNat 8 (cb.take 8) (cb.drop 8) (by simp; omega) $$ [C0 C8]
  · iframe C0 C8
  rw [List.take_append_drop]
  iexact C



end L322

end WNear.Binary.SerdeErrBox
