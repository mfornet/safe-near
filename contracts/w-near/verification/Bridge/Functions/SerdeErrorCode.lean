import Bridge.Functions.SerdePositionPositive
import Bridge.Functions.SerdeErrRet
import Bridge.Functions.BorshLeaves

/-!
# Syntax errors preserve the exact error code and source position

`positionedBox` retains the exact twelve input code bytes and the nonzero
source line. `heapPos` combines those resources with the allocation invariant.
This strengthens `SerdeErrorPositioned` so drop glue can distinguish syntax
errors from variants that own a message.
-/

namespace WNear.Binary.SerdeErrorCode

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeErrBox
open WNear.Binary.SerdePositionPositive
open WNear.Binary.SerdePosition (cost638 cost645)
open WNear.Binary.SerdeRead (rd)

theorem bytes32_decode (bs : List UInt8) (h : bs.length = 4) :
    bytes32 (UInt32.ofNat (Memory.decodeLE bs)) = bs := by
  match bs, h with
  | [a, b, c, d], _ =>
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
    simp only [bytes32, storeBytes, storeRaw, Memory.decodeLE, List.foldr, List.range,
      List.range.loop, List.map, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp <;> omega)

theorem copy_code (cb : List UInt8) (hcb : cb.length = 12) :
    storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb))) = cb := by
  rw [BorshLeaves.storeBytes_i64_decode _ (by simp; omega), bytes32_decode _ (by simp; omega),
    List.take_append_drop]

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- An error box with a source line already attached. -/
def positionedBox (n : Nat) (p : UInt32) (code : List UInt8) : IProp GF :=
  iprop(∃ (line col : UInt32),
    ⌜p.toNat + 20 ≤ 2 ^ 32 ∧ code.length = 12 ∧ line ≠ 0⌝ ∗
    n ↦[wms][ p.toNat ] code ∗ n ↦[i32][ p.toNat + 12 ] line ∗ n ↦[i32][ p.toNat + 16 ] col)

/-- The fresh error allocation with its position retained. -/
def heapPos (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (p : UInt32) (code : List UInt8) : IProp GF :=
  iprop(heapR n maxP len live F 20 p ∗ positionedBox n p code)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `Error::syntax` preserves the supplied nonzero line in its allocated box. -/
theorem f639_positioned (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp e line col idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (eb : List UInt8) (heb : eb.length = 12) (he : e.toNat + 12 ≤ 2 ^ 32)
    (hsp : 48 ≤ sp.toNat) (hr : roomFor4 len maxP 20) (hline : line ≠ 0) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 625 ↪[wf] FuncInst.wasm types[45]! inst f625 ∗ A 624 ↪[wf] FuncInst.wasm types[31]! inst f624 ∗
      A 590 ↪[wf] FuncInst.wasm types[32]! inst f590
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f639 Cg
        (fun args => iprop(⌜args = [.i32 e, .i32 line, .i32 col]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ e.toNat ] eb))
        (fun _ => 140 * cfg.regularOpCost + AllocWalk.cost310W cfg F 20 4)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 48) 48 ∗ vt n 1057464 idx ta (A 578) ∗ heapPos n maxP len live F p eb ∗
          n ↦[wms][ e.toNat ] eb)) := by
  iintro ⟨#Hcode, #H310, #H625, #H624, #H590⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha590 := hm.funcs 590 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, He⟩
  subst hargs
  icases U128From.memBytes_split n e.toNat 8 eb (by omega) $$ He with ⟨E0, E8⟩
  simp only [f639]
  generalize hK : AllocWalk.cost310W cfg F 20 4 = K
  have key := f590_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt sp 20 idx
    maxP len live F hsp (by decide) (by decide) hr
  rw [hK] at key
  clear hK
  rw [show 140 * cfg.regularOpCost + K + R = 140 * cfg.regularOpCost + (K + R) by omega]
  mstep
  mcall key using [Hg Hs Hvt Hinv]
  · iframe Hg Hs Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0⟩, Hg, Hs, Hvt, HA⟩
  subst hrs
  clear key
  mcredits (28 * cfg.regularOpCost + R)
  iunfold heapA at HA
  icases HA with ⟨HR, Hb⟩
  ihave HR := heapR_bound n maxP len live F 20 p $$ HR
  icases HR with ⟨%hpb, HR⟩
  rw [show UInt32.toNat 20 = 20 from rfl] at hpb ⊢
  icases block_split20 n p.toNat $$ Hb with ⟨%b0, %b8, %b12, %b16, %⟨h0, h8, h12, h16⟩, B0, B8, B12, B16⟩
  mstep; mstep
  mstep [B16]
  mstep; mstep; mstep [B12]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [E8] with (simp [UInt32.toNat_add]; omega)
  mstep [B8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [E0]
  mstep [B0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iexists p
  isplitr
  · ipureintro; exact ⟨by simp [htype], hp0⟩
  iframe Hg Hs Hvt
  isplitr [E0 E8]
  · iunfold heapPos
    iframe HR
    iunfold positionedBox
    ihave BC := U128From.memBytes_join n p.toNat 8
      (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 eb)))) 8)
      (bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 eb)))) (by simp [storeBytes]) $$ [B0 B8]
    · iframe B0 B8
    rw [copy_code eb heb]
    iexists line, col
    iframe BC B12 B16
    ipureintro
    exact ⟨hpb.le, heb, hline⟩
  ihave E := U128From.memBytes_join n e.toNat 8 (eb.take 8) (eb.drop 8) (by simp; omega) $$ [E0 E8]
  · iframe E0 E8
  rw [List.take_append_drop]
  iexact E


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem f325_positioned (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapPos n maxP len live F p cb ∗
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
  have key638 := f638_pos (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg (A 583) (A 609) (A 645)
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
  icases HQ with ⟨%hrs, Hg, S48, ⟨%line, %col, %hline, L0, L4⟩, Hrd⟩
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
  have key639 := f639_positioned (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) (sp - 32 + 16) line col idx maxP len live F
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes])
    (by rw [UInt32.toNat_add, h32]; simp; omega) (by omega) hr hline
  rw [copy_code cb hcb, hK2] at key639
  clear hK2
  ihave S48 := stk_addr (show (sp - 32).toNat - 48 = (sp - 32).toNat - 48 by rfl) $$ S48
  rw [copy_code cb hcb]
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
    rw [hcb]
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



set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem f322_positioned (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
          stk n (sp.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapPos n maxP len live F p cb ∗
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
  have key638 := f640_pos (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg (A 583) (A 609) (A 645)
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
  icases HQ with ⟨%hrs, Hg, S48, ⟨%line, %col, %hline, L0, L4⟩, Hrd⟩
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
  have key639 := f639_positioned (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) (sp - 32 + 16) line col idx maxP len live F
    (storeBytes (Value.i64 (UInt64.ofNat (Memory.decodeLE (List.take 8 cb)))) 8 ++
      bytes32 (UInt32.ofNat (Memory.decodeLE (List.drop 8 cb)))) (by simp [storeBytes])
    (by rw [UInt32.toNat_add, h32]; simp; omega) (by omega) hr hline
  rw [copy_code cb hcb, hK2] at key639
  clear hK2
  ihave S48 := stk_addr (show (sp - 32).toNat - 48 = (sp - 32).toNat - 48 by rfl) $$ S48
  rw [copy_code cb hcb]
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
    rw [hcb]
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



end Proof

end WNear.Binary.SerdeErrorCode
