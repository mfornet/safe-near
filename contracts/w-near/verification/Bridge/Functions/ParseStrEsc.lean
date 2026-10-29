import Bridge.Functions.ParseEscape
import Bridge.Functions.StrCost

/-!
# `parse_str` (646) on every input (M6)

`ParseStrErr.f646_spec_noesc` proved 646 on every escape-free input. With the escapes (`parse_escape`,
649, `ParseEscape.f649_spec`) and the scratch's growth (`ScratchGrow`), the outer loop of 646 runs
once per escape: scan the plain bytes, append them to the scratch (613), decode the escape into the
scratch (649), and go on. At `"` with a non-empty scratch the last plain bytes are appended (613) and
the scratch is validated (728, then `as_str` 648): `Ok(Reference::Copied)`.

* `resStr`: the result, by the run's outcome `strRun (bs.drop i) []` (`StrModel`): `Ok(Borrowed)`
  when the string has no escape, `Ok(Copied)` holding the bytes in the scratch otherwise, both when the
  bytes are UTF-8; else `Err(box)`.
* `f646_spec`: the specification, at `costRun` (`StrCost`).
-/

namespace WNear.Binary.SerdeErrBox

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.FromUtf8 (res927 cost927)
open WNear.Binary.FromUtf8Gen (utf8Width)

section L648m

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`as_str`** (648) on bytes `ws` anywhere in memory that are not UTF-8: `from_utf8` fails, then
`InvalidUnicodeCodePoint` through 657 at the reader's index. -/
theorem f648_spec_bad_mem (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr p len idx : UInt32) (ob ibs ws : List UInt8) (i : Nat) (maxP mlen : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hi : i ≤ ibs.length) (hlen : ibs.length + 1 < 2 ^ 32)
    (hptr : ptr.toNat + ibs.length ≤ 2 ^ 32) (hws : ws.length = len.toNat) (hp : p.toNat + len.toNat ≤ 2 ^ 32)
    (hbad : Utf8.utf8Ok ws = false) (hsp : 112 ≤ sp.toNat)
    (hr : roomFor4 mlen maxP 20) :
    errCode n maxP inst mi A ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗
      A 657 ↪[wf] FuncInst.wasm types[31]! inst f657
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f648 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 p, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr ibs i ∗ n ↦[wms][ p.toNat ] ws ∗ n ↦[wms][ 1071704 ] utf8Width))
        (fun _ => (60 + cost927 len.toNat) * cfg.regularOpCost + costErr cfg F i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ q : UInt32, ⌜q ≠ 0⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapA n maxP mlen live F 20 q ∗
          n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] q ∗ rd n de ptr ibs i ∗
          n ↦[wms][ p.toNat ] ws ∗ n ↦[wms][ 1071704 ] utf8Width)) := by
  iintro ⟨Hcode, #H927, #H657⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #H583, #H609, #H645, #H638⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha927 := hm.funcs 927 (by decide)
  have ha657 := hm.funcs 657 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hrd, Bs, Ht⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 112) 80 32 $$ Hs with ⟨S80, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80) 12 20 $$ Hs with ⟨SO, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80 + 12) 4 16 $$ Hs with ⟨S4, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80 + 12 + 4) 4 12 $$ Hs with ⟨SC0, Hs⟩
  icases stk_split n (sp.toNat - 112 + 80 + 12 + 4 + 4) 8 4 $$ Hs with ⟨SC8, S4'⟩
  iunfold stk at SO SC0 SC8
  icases SO with ⟨%so, %hso, SO⟩
  icases SC0 with ⟨%sc0, %hsc0, SC0⟩
  icases SC8 with ⟨%sc8, %hsc8, SC8⟩
  simp only [f648]
  rw [show (60 + cost927 len.toNat) * cfg.regularOpCost + costErr cfg F i + R =
    60 * cfg.regularOpCost + (cost927 len.toNat * cfg.regularOpCost + (costErr cfg F i + R)) by
      rw [Nat.add_mul]; omega]
  generalize hE : costErr cfg F i = E
  have hK3 : (16 + cost927 len.toNat) * cfg.regularOpCost = 16 * cfg.regularOpCost + cost927 len.toNat * cfg.regularOpCost :=
    Nat.add_mul _ _ _
  ihave SO := AllocNewCell.memBytes_addr (show sp.toNat - 112 + 80 = (sp - 32).toNat by omega) $$ SO
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall (FromUtf8Gen.f927_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 32) p len so
    ws hso (by omega) hws hp) using [SO Bs Ht]
  · iframe SO Bs Ht
  rw [hK3]
  clear hK3
  generalize cost927 len.toNat * cfg.regularOpCost = K
  mcredits (36 * cfg.regularOpCost + (E + R))
  icases HQ with ⟨%hrs, Bs, Hres, Ht⟩
  subst hrs
  iunfold res927 at Hres
  rw [hbad]
  simp only [Bool.false_eq_true, ite_false]
  icases Hres with ⟨%eb, %heb, R0, R4⟩
  mstep; mstep
  mstep; mstep [R0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep
  mstep; mstep
  mstep [SC0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep; mstep
  ihave C := U128From.memBytes_join n (sp.toNat - 112 + 80 + 12 + 4) 4 (bytes32 14) sc8 (by simp) $$ [SC0 SC8]
  · iframe SC0 SC8
  ihave C := AllocNewCell.memBytes_addr (show sp.toNat - 112 + 80 + 12 + 4 = (sp - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ C
  ihave S80 := stk_addr (show sp.toNat - 112 = (sp - 32).toNat - 80 by omega) $$ S80
  have key := f647_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) out de (sp - 32 + 16) ptr idx ob (bytes32 14 ++ sc8) ibs i maxP mlen live F hob hout (by simp; omega)
    (by rw [UInt32.toNat_add, h32]; simp; omega) hde hi hlen hptr (by omega) hr
  rw [← f657_eq, hE] at key
  unfold errCode at key
  mcall key using [Hg S80 Hvt Hinv Ho C Hrd]
  · iframe Hg S80 Hvt Hinv Ho C Hrd
  clear key
  mcredits (11 * cfg.regularOpCost + R)
  icases HQ with ⟨%hrs, %q, %hq, Hg, S80, Hvt, HA, O0, O4, C, Hrd⟩
  subst hrs
  mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists q
  isplitr
  · ipureintro; exact hq
  iframe Hg Hvt HA O0 O4 Hrd Ht Bs
  ihave R0 := stk_word n _ _ $$ R0
  ihave R4 := stk_intro n _ _ $$ R4
  rw [heb]
  ihave SO := stk_join n (sp - 32).toNat 4 8 $$ [R0 R4]
  · iframe R0 R4
  ihave SO := stk_addr (show (sp - 32).toNat = sp.toNat - 112 + 80 by omega) $$ SO
  ihave J1 := stk_join n (sp.toNat - 112 + 80) 12 4 $$ [SO S4]
  · iframe SO S4
  ihave C := stk_intro n _ _ $$ C
  ihave C := stk_addr (show (sp - 32 + 16).toNat = sp.toNat - 112 + 80 + 16 by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ C
  rw [show (bytes32 14 ++ sc8).length = 12 by simp; omega]
  ihave J2 := stk_join n (sp.toNat - 112 + 80) 16 12 $$ [J1 C]
  · iframe J1 C
  ihave S4' := stk_addr (show sp.toNat - 112 + 80 + 12 + 4 + 4 + 8 = sp.toNat - 112 + 80 + 28 by omega) $$ S4'
  ihave J3 := stk_join n (sp.toNat - 112 + 80) 28 4 $$ [J2 S4']
  · iframe J2 S4'
  ihave S80 := stk_addr (show (sp - 32).toNat - 80 = sp.toNat - 112 by omega) $$ S80
  iapply stk_join n (sp.toNat - 112) 80 32
  iframe S80 J3

end L648m

end WNear.Binary.SerdeErrBox

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
open WNear.Binary.ScratchGrow (sbuf sgCode capAfter fAfter hlAfter roomRes costExt)
open WNear.Binary.ParseEscape (escDecode escK sbufE escCode res649 f649_spec cost649)
open WNear.Binary.SerdeEsc (hexTable)

/-- The run stops first at a `"`: the string has no escape, its slice is borrowed. -/
def borrowed (l : List UInt8) : Prop := (l.dropWhile plain).head? = some 0x22

instance (l : List UInt8) : Decidable (borrowed l) := by unfold borrowed; infer_instance

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 646's `Err(box)`: the box, the reader somewhere, the scratch in some state with the box after it. -/
def errStr (n maxP hl : Nat) (live : List (Nat × Nat)) (out de ptr sc : UInt32) (ob bs : List UInt8) :
    IProp GF :=
  iprop(∃ (box p cap : UInt32) (j hl' F' : Nat) (acc : List UInt8), ⌜box ≠ 0 ∧ j ≤ bs.length ∧ hl ≤ hl'⌝ ∗
    n ↦[i32][ out.toNat ] 1 ∗ n ↦[i32][ out.toNat + 4 ] box ∗ n ↦[wms][ out.toNat + 8 ] (ob.drop 8) ∗
    rd n de ptr bs j ∗ n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗
    n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbufE n maxP hl' live F' p cap acc box)

/-- 646's result on any input, by the run's outcome. -/
def resStr (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (out de ptr sc ptrS capS : UInt32)
    (ob bs : List UInt8) (i : Nat) : IProp GF :=
  match strRun (bs.drop i) [] with
  | .ok bytes rest =>
    if Utf8.utf8Ok bytes = true then
      iprop(n ↦[i32][ out.toNat ] 0 ∗ rd n de ptr bs (bs.length - rest.length) ∗
        n ↦[i32][ out.toNat + 12 ] UInt32.ofNat bytes.length ∗
        if borrowed (bs.drop i) then
          iprop(n ↦[i32][ out.toNat + 4 ] 0 ∗ n ↦[i32][ out.toNat + 8 ] (ptr + UInt32.ofNat i) ∗
            n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗ n ↦[i32][ sc.toNat + 8 ] 0 ∗
            sbuf n maxP hl live F ptrS capS [])
        else
          iprop(∃ (p cap : UInt32) (hl' F' : Nat), ⌜hl ≤ hl'⌝ ∗ n ↦[i32][ out.toNat + 4 ] 1 ∗
            n ↦[i32][ out.toNat + 8 ] p ∗ n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗
            n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat bytes.length ∗ sbuf n maxP hl' live F' p cap bytes))
    else errStr n maxP hl live out de ptr sc ob bs
  | _ => errStr n maxP hl live out de ptr sc ob bs

/-- The code 646 runs (persistent). -/
def code646 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(errCode n maxP inst mi A ∗ escCode n maxP inst mi A ∗ A 927 ↪[wf] FuncInst.wasm types[31]! inst f927 ∗
    A 657 ↪[wf] FuncInst.wasm types[31]! inst f657 ∗ A 647 ↪[wf] FuncInst.wasm types[31]! inst f647 ∗
    A 648 ↪[wf] FuncInst.wasm types[45]! inst f648 ∗ A 728 ↪[wf] FuncInst.wasm types[14]! inst f728)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (code646 (GF := GF) n maxP inst mi A) := by
  unfold code646 errCode; infer_instance

end Defs

section L728

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem sbuf_bytes {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {p cap : UInt32} {bs : List UInt8} :
    sbuf (GF := GF) n maxP hl live F p cap bs ⊢ ⌜p.toNat + bs.length < 2 ^ 32⌝ ∗ n ↦[wms][ p.toNat ] bs ∗
      (n ↦[wms][ p.toNat ] bs -∗ sbuf n maxP hl live F p cap bs) := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%h, Hb, Hj, Hinv⟩
  isplitr
  · ipureintro; omega
  iframe Hb
  iintro Hb
  iunfold sbuf
  iframe Hb Hj Hinv
  ipureintro; exact h

theorem sbufR_bytes {n : Nat} {p cap : UInt32} {bs : List UInt8} :
    ParseEscape.sbufR (GF := GF) n p cap bs ⊢ ⌜p.toNat + bs.length < 2 ^ 32⌝ ∗ n ↦[wms][ p.toNat ] bs ∗
      (n ↦[wms][ p.toNat ] bs -∗ ParseEscape.sbufR n p cap bs) := by
  iintro H
  iunfold ParseEscape.sbufR at H
  icases H with ⟨%h, Hb, Hj⟩
  isplitr
  · ipureintro; omega
  iframe Hb
  iintro Hb
  iunfold ParseEscape.sbufR
  iframe Hb Hj
  ipureintro; exact h

/-- **`Vec::deref(out, vec)`** (728): `(ptr, len)` at `out`. -/
theorem f728_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec p len : UInt32) (ob : List UInt8) (hob : ob.length = 8) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f728 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 vec]⌝ ∗ n ↦[wms][ out.toNat ] ob ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 8 ] len))
        (fun _ => 10 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] len ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 8 ] len)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho, V0, V8⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  simp only [f728]
  mstep; mstep; mstep [V8]; mstep [O4]
  mstep; mstep; mstep [V0]; mstep [O0]
  mcredits R
  iframe Hc O0 O4 V0 V8

end L728

theorem costErr_monoF (cfg : WasmConfig) (F F' i : Nat) (h : F ≤ F') : costErr cfg F i ≤ costErr cfg F' i := by
  unfold costErr AllocWalk.cost310W AllocWalk.walkCost
  have := AllocWalk.wc_mono cfg h
  omega

theorem cost927_mono (a b : Nat) (h : a ≤ b) : cost927 a ≤ cost927 b := by unfold cost927; omega

theorem run_split (l : List UInt8) : l = l.takeWhile plain ++ l.dropWhile plain :=
  (List.takeWhile_append_dropWhile).symm

theorem hlAfter_le (hl hl' : Nat) (cap len k : UInt32) (h : hlAfter hl hl' cap len k) : hl ≤ hl' := by
  unfold hlAfter at h
  split at h
  · omega
  · rcases h with h | h
    · omega
    · rw [h]; unfold VecFromElem.grownLen; omega

theorem capAfter_le (cap len k : UInt32) (hc : cap.toNat < 2 ^ 28) (hlk : len.toNat + k.toNat < 2 ^ 28) :
    (capAfter cap len k).toNat ≤ max cap.toNat (2 * (len.toNat + k.toNat) + 8) := by
  unfold capAfter
  split
  · omega
  · rename_i hfit
    simp only [ScratchGrow.fits] at hfit
    rw [VecGrow.growCap_toNat _ _ (by omega)]
    have : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
    rw [this]
    omega

theorem costBase_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) (L : Nat) :
    costBase cfg F cap acc l L ≤ costRun cfg F cap acc l L := by
  cases hd : l.dropWhile plain with
  | nil => rw [costRun_stop cfg F cap acc l L (by intro r; rw [hd]; simp)]
  | cons x rest =>
    by_cases hx : x = 0x5C
    · subst hx; rw [costRun_esc cfg F cap acc l rest L hd]; omega
    · rw [costRun_stop cfg F cap acc l L (by intro r; rw [hd]; simp; intro e; exact absurd e hx)]

section L646e

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
/-- **`SliceRead::parse_str(out, rd, scratch)`** (646) on every input, the scratch empty: `resStr`, at
`costRun`. -/
theorem f646_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr idx ptrS capS : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 192 ≤ sp.toNat) (hi : i ≤ bs.length) (hcapS : capS.toNat < 2 ^ 25)
    (hroom : roomRun maxP hl capS [] (bs.drop i)) :
    code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 192) 192 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ sbuf n maxP hl live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] hexTable))
        (fun _ => costRun cfg F capS [] (bs.drop i) bs.length + 100 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 192) 192 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] hexTable ∗ resStr n maxP hl live F out de ptr sc ptrS capS ob bs i)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold code646 at Hk'
  icases Hk' with ⟨#HE, #HC, #F927, #F657, #F647, #F648, #F728⟩
  ihave #HE' := HE
  iunfold errCode at HE'
  icases HE' with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #F583, #H609, #H645, #H638⟩
  ihave #HC' := HC
  iunfold escCode at HC'
  icases HC' with ⟨#HG, -, -, -, #F649⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #F613, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha583 := hm.funcs 583 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha647 := hm.funcs 647 (by decide)
  have ha648 := hm.funcs 648 (by decide)
  have ha649 := hm.funcs 649 (by decide)
  have ha728 := hm.funcs 728 (by decide)
  have ha927 := hm.funcs 927 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t36 : types[36]!.params.length = 6 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Ho, Hrd, S0, S4, S8, Hsb, He, Hw, Ht⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  simp only [f646]
  generalize hRl : 60 * cfg.regularOpCost + R = Rl
  rw [show costRun cfg F capS [] (bs.drop i) bs.length + 100 * cfg.regularOpCost + R =
    40 * cfg.regularOpCost + (costRun cfg F capS [] (bs.drop i) bs.length + Rl) by omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := costRun cfg F capS [] (bs.drop i) bs.length + Rl)
    (I := fun X fr => iprop(∃ (j : Nat) (acc : List UInt8) (p cap : UInt32) (hl' F' : Nat)
        (a4 a5 a6 a7 a8 a9 : UInt32),
      ⌜X = [] ∧ fr = fr646 inst mi out de sc (sp - 48) a4 a5 a6 a7 a8 a9 ∧ i ≤ j ∧ j ≤ bs.length ∧
        strRun (bs.drop j) acc = strRun (bs.drop i) [] ∧
        (acc = [] → j = i ∧ p = ptrS ∧ cap = capS ∧ hl' = hl ∧ F' = F) ∧ (j = i → acc = []) ∧ (j ≠ i → ¬ borrowed (bs.drop i)) ∧
        acc.length ≤ j - i ∧ cap.toNat ≤ max capS.toNat (2 * acc.length + 8) ∧ hl ≤ hl' ∧
        roomRun maxP hl' cap acc (bs.drop j)⌝ ∗
      credits Cg (costRun cfg F' cap acc (bs.drop j) bs.length + Rl) ∗ stk n (sp.toNat - 192) 192 ∗
      n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
      n ↦[wms][ 1062712 ] hexTable ∗ vt n 1057464 idx ta (A 578) ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩ ∗
      n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
      n ↦[i32][ de.toNat + 8 ] UInt32.ofNat j ∗ n ↦[wms][ ptr.toNat ] bs ∗
      n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗ n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗
      sbuf n maxP hl' live F' p cap acc)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%j, %acc, %p, %cap, %hl', %F', %a4, %a5, %a6, %a7, %a8, %a9,
      %⟨hX, hfr, hij, hjl, hrun, hacc0, hj0, hjb, haccl, hcapb, hhl, hroomj⟩,
      Hc, Hs, Ho, He, Hw, Ht, Hvt, Hg, D0, D4, D8, Hb, S0, S4, S8, Hsb⟩
    subst hX
    rw [hfr]
    simp only [fr646]
    clear hfr
    have hsplit := run_split (bs.drop j)
    have hcr := costBase_le cfg F' cap acc (bs.drop j) bs.length
    unfold costBase at hcr
    generalize hbody : (bs.drop j).takeWhile plain = body at hsplit hcr
    rw [Nat.add_mul (500 + 30 * body.length)] at hcr
    generalize htail : (bs.drop j).dropWhile plain = tail at hsplit
    have hplain : ∀ b ∈ body, plain b = true := by rw [← hbody]; exact takeWhile_plain _
    have hstop : ∀ x rest, tail = x :: rest → plain x = false := fun x rest h =>
      dropWhile_head _ x rest (by rw [htail, h])
    have hil : j + body.length ≤ bs.length := by
      have := congrArg List.length hsplit; simp at this; omega
    have htl : j + body.length + tail.length = bs.length := by
      have := congrArg List.length hsplit; simp at this; omega
    have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat j)) = 0
        then Value.i32 (UInt32.ofNat j) else Value.i32 (UInt32.ofNat bs.length)) = Value.i32 (UInt32.ofNat bs.length) := by
      by_cases hib : j = bs.length
      · rw [hib]; split <;> rfl
      · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat j)) ≠ 0 := by
          simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
        rw [if_neg this]
    generalize hZ : costRun cfg F' cap acc (bs.drop j) bs.length - (500 + 30 * body.length) * cfg.regularOpCost = Z
    have hZ' : costRun cfg F' cap acc (bs.drop j) bs.length = (500 + 30 * body.length) * cfg.regularOpCost + Z := by
      have := Nat.le_add_right ((500 + 30 * body.length) * cfg.regularOpCost) 0
      omega
    rw [hZ', show (500 + 30 * body.length) * cfg.regularOpCost + Z + Rl =
      40 * cfg.regularOpCost + (30 * (j + body.length - j) * cfg.regularOpCost + 450 * cfg.regularOpCost +
        (Z + Rl) + 10 * cfg.regularOpCost) by
      rw [show j + body.length - j = body.length by omega]; simp only [Nat.add_mul]; omega]
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
    iapply MemCpy.mwpi_loop0 (Cg := Cg)
      (R := 30 * (j + body.length - j) * cfg.regularOpCost + 450 * cfg.regularOpCost + (Z + Rl))
      (I := invS n inst mi Cg cfg.regularOpCost 450 (Z + Rl) out de sc (sp - 48) (UInt32.ofNat bs.length)
        (UInt32.ofNat j) (UInt32.ofNat bs.length) ptr j body.length
        iprop(stk n (sp.toNat - 192) 192 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] hexTable ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
          n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩ ∗
          n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl' live F' p cap acc)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold invS at HI
      icases HI with ⟨%k, %l9, %⟨hX, hfr, hik, hkm⟩, Hc, D8, HP⟩
      subst hX
      rw [hfr]
      simp only [fr646]
      clear hfr
      icases HP with ⟨Hs, Ho, He, Hw, Ht, Hvt, D0, D4, Hb, Hg, S0, S4, S8, Hsb⟩
      by_cases hkl : k < bs.length
      · have hne : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat bs.length) (UInt32.ofNat k)) = 0 := by
          have hu : (UInt32.ofNat k).toNat = k := by simp; omega
          have hv : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
          generalize UInt32.ofNat k = u at hu ⊢
          generalize UInt32.ofNat bs.length = v at hv ⊢
          have : v ≠ u := fun e => by subst e; omega
          simp [Numeric.bool, Numeric.irelop32, this]
        have hbk : bs[k]? = (body ++ tail)[k - j]? := by
          rw [← hsplit, List.getElem?_drop]; congr 1; omega
        ihave Hb := MemCpy.memBytes_pick n ptr.toNat k bs hkl $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
        rw [hxk]
        rw [List.getElem?_eq_getElem hkl, hxk] at hbk
        have es : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
        have hx256 := x.toNat_lt
        by_cases hkm' : k < j + body.length
        · have hxb : plain x = true := by
            rw [List.getElem?_append_left (by omega)] at hbk
            exact hplain x (List.mem_of_getElem? hbk.symm)
          rw [show 30 * (j + body.length - k) * cfg.regularOpCost + 450 * cfg.regularOpCost + (Z + Rl) =
            480 * cfg.regularOpCost + (30 * (j + body.length - (k + 1)) * cfg.regularOpCost + (Z + Rl)) by
              rw [show j + body.length - k = (j + body.length - (k + 1)) + 1 by omega]
              simp only [Nat.mul_add, Nat.add_mul]; omega]
          generalize hZ2 : 30 * (j + body.length - (k + 1)) * cfg.regularOpCost = Z2
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
          iapply invS_intro n inst mi Cg cfg.regularOpCost 450 (Z + Rl) out de sc (sp - 48) _ _ _ ptr j body.length _ (k + 1) _
            (by omega) (by omega)
          iframe D8 Hs Ho He Hw Ht Hvt D0 D4 Hb Hg S0 S4 S8 Hsb
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · -- the scan stops at `x`, the first byte of `tail`
          have hk : k = j + body.length := by omega
          have htx : ∃ rest, tail = x :: rest := by
            rw [List.getElem?_append_right (by omega), show k - j - body.length = 0 by omega] at hbk
            cases htl' : tail with
            | nil => rw [htl'] at hbk; simp at hbk
            | cons y rest => rw [htl'] at hbk; simp at hbk; exact ⟨rest, by simp [hbk]⟩
          obtain ⟨rest, htx⟩ := htx
          have hxp := hstop x rest htx
          rw [show 30 * (j + body.length - k) * cfg.regularOpCost = 0 by rw [show j + body.length - k = 0 by omega]; simp,
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
          mstep; mstep; mstep; mstep
          by_cases hx92 : x.toNat = 92
          · -- `\`: an escape
            have hx : x = 0x5C := UInt8.toNat_inj.mp (by rw [hx92]; rfl)
            subst hx
            have h92 : Numeric.bool (Numeric.irelop32 IRelOp.eq (0x5C : UInt8).toUInt32 92) ≠ 0 := by decide
            have hcb := costRun_esc cfg F' cap acc (bs.drop j) rest bs.length (by rw [htail, htx])
            unfold costBase at hcb
            rw [hbody, Nat.add_mul (500 + 30 * body.length)] at hcb
            have hrest : bs.drop (k + 1) = rest := by
              rw [hk, show j + body.length + 1 = j + (body.length + 1) by omega, ← List.drop_drop, hsplit, htx]; simp
            have hroom1 := (roomRun_unfold maxP hl' cap acc (bs.drop j)).mp hroomj
            rw [hbody] at hroom1
            have hd5c : (bs.drop j).dropWhile plain = 0x5C :: rest := by rw [htail, htx]
            iapply mwpi_cons
            iapply mwpi_br_if_taken'
            isplitr
            · ipureintro; exact ⟨rfl, h92⟩
            mctrl_norm
            repeat mpay
            icases stk_split n (sp.toNat - 192) 144 48 $$ Hs with ⟨T144, T48⟩
            rw [show sp.toNat - 192 + 144 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 24 24 $$ T48 with ⟨T24, T24b⟩
            icases stk_split n ((sp - 48).toNat + 24) 8 16 $$ T24b with ⟨T8e, T16b⟩
            iunfold stk at T8e
            icases T8e with ⟨%w8, %hw8, T8e⟩
            ihave T8e := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 24 = (sp - 48 + 24).toNat by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ T8e
            mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
            mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48 + 24) (UInt32.ofNat j)
              (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062216 w8 hw8 (by rw [UInt32.toNat_add, h48]; simp; omega)
              (by simp; omega) (by simp; omega)) using [T8e]
            · iframe T8e
            icases HQ with ⟨%hrs, P0, P4⟩
            subst hrs
            mcredits (300 * cfg.regularOpCost + (Z + Rl))
            ihave P0 := AllocNewCell.memBytes_addr (show (sp - 48 + 24).toNat = (sp - 48).toNat + 24 by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ P0
            ihave P4 := AllocNewCell.memBytes_addr (show (sp - 48 + 24).toNat + 4 = (sp - 48).toNat + 28 by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ P4
            rw [show UInt32.ofNat k - UInt32.ofNat j = UInt32.ofNat body.length by
              apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
            mstep; mstep; mstep [P0]; mstep; mstep [P4]
            have hsplit' : bs.drop j = body ++ 0x5C :: rest := by rw [hsplit, htx]
            have hab : (acc ++ body).length = acc.length + body.length := List.length_append
            ihave Hb := U128From.memBytes_split n ptr.toNat j bs (by omega) $$ Hb
            icases Hb with ⟨B0, Bd⟩
            rw [hsplit']
            ihave Bd := U128From.memBytes_split n (ptr.toNat + j) body.length (body ++ 0x5C :: rest) (by simp) $$ Bd
            icases Bd with ⟨Bbody, Brest⟩
            rw [List.take_left' rfl, List.drop_left' rfl]
            ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + j = (ptr + UInt32.ofNat j).toNat by
              simp [UInt32.toNat_add]; omega) $$ Bbody
            icases stk_split n (sp.toNat - 192) 32 112 $$ T144 with ⟨T32a, T112⟩
            ihave T112 := stk_addr (show sp.toNat - 192 + 32 = (sp - 48).toNat - 112 by omega) $$ T112
            have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
            have hcapl : cap.toNat < 2 ^ 27 := by omega
            have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
              (sp - 48) sc (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) p cap idx maxP hl' live F' acc body
              (by omega) (by omega) hcapl (by rw [hm32]; omega) hm32.symm (by simp [UInt32.toNat_add]; omega) hroom1.2.1
            rw [show Z + Rl = costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) +
              (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl) by omega]
            mcall key using [Hg T112 Hvt S0 S4 S8 Hsb Bbody]
            · iframe Hg T112 Hvt S0 S4 S8 Hsb Bbody
            clear key
            icases HQ with ⟨%hrs, %p1, %hl1, %hhl1, Hg, T112, Hvt, S0, S4, S8, Hsb, Bbody⟩
            subst hrs
            rw [hm32]
            have hl1le := hlAfter_le _ _ _ _ _ hhl1
            have hroom2 := hroom1.2.2 hl1 hhl1
            have hroom3 := hroom2.2 rest hd5c
            mcredits (200 * cfg.regularOpCost + (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl))
            mstep; mstep [D8]
            mstep; mstep; mstep; mstep; mstep; mstep
            rw [SerdeRead.ofNat_succ k (by omega)]
            have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (k + 1)) (UInt32.ofNat k)) = 0 := by
              rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
            brn hov
            clear hov
            mstep; mstep; mstep [D8]
            ihave Hrd : rd n de ptr bs (k + 1) $$ [D0 D4 D8 B0 Bbody Brest]
            · iunfold rd, sliceRead
              iframe D0 D4 D8
              ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                simp [UInt32.toNat_add]; omega) $$ Bbody
              ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (92 :: rest) rfl $$ [Bbody Brest]
              · iframe Bbody Brest
              rw [← hsplit']
              ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
              · iframe B0 Bd
              rw [List.take_append_drop]
              iexact Bb
            ihave T144 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 192 + 32 by omega) $$ T112
            ihave T144 := stk_join n (sp.toNat - 192) 32 112 $$ [T32a T144]
            · iframe T32a T144
            ihave T144 := stk_addr (show sp.toNat - 192 = (sp - 48).toNat - 144 by omega) $$ T144
            rw [show UInt32.ofNat (acc.length + body.length) = UInt32.ofNat (acc ++ body).length by simp] at *
            generalize hcap1 : capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = cap1 at hroom3 hcb ⊢
            generalize hF1 : fAfter F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = F1 at hcb ⊢
            have hcap1b : cap1.toNat ≤ max capS.toNat (2 * (acc ++ body).length + 8) := by
              have := capAfter_le cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) (by omega) (by simp; omega)
              rw [hcap1] at this
              simp at this ⊢
              omega
            have key := f649_spec (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt
              (sp - 48) de ptr sc p1 cap1 idx bs (acc ++ body) (k + 1) maxP hl1 live F1 hde (by omega) hsc (by omega)
              hptr (by omega) (by omega) (by simp; omega) hroom2.1 (by rw [hrest]; exact hroom3.1)
            have hc649 : cost649 cfg F1 cap1 (acc ++ body) bs (k + 1) = costEsc cfg F1 cap1 (acc ++ body) rest bs.length := by
              unfold cost649 costEsc; rw [hrest]
            rw [hc649] at key
            rw [show Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl =
              costEsc cfg F1 cap1 (acc ++ body) rest bs.length +
              (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                costEsc cfg F1 cap1 (acc ++ body) rest bs.length + Rl) by omega]
            mstep; mstep
            mcall key using [Hg T144 Hvt Hrd S0 S4 S8 Hsb Ht]
            · iframe Hg T144 Hvt Hrd S0 S4 S8 Hsb Ht
            clear key
            icases HQ with ⟨Hg, T144, Hvt, Ht, HQ⟩
            mcredits (150 * cfg.regularOpCost + (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                costEsc cfg F1 cap1 (acc ++ body) rest bs.length + Rl))
            cases he : escDecode rest with
            | none =>
              -- the escape is bad: `Err(box)`
              simp only [res649, hrest, he]
              icases HQ with ⟨%q, %j', %⟨hrs, hq, hj'⟩, Hrd, S0, S4, S8, HE'⟩
              subst hrs
              have hres : strRun (bs.drop i) [] = .badEsc := by
                rw [← hrun, strRun_cons _ _ 0x5C rest (by rw [htail, htx])]; simp [he]
              have hq' : Numeric.bool (q == 0) = 0 := by simp [Numeric.bool, hq]
              icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
              icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
              mstep; mstep
              brn (by simpa using hq')
              repeat mstep
              mstep [O0]
              repeat mstep
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
              iframe Hg Hvt He Hw Ht
              isplitr [O0 O4 O8 Hrd S0 S4 S8 HE']
              · ihave P0 := stk_word n ((sp - 48).toNat + 24) _ $$ P0
                ihave P4 := stk_word n ((sp - 48).toNat + 28) _ $$ P4
                ihave P8 := stk_join n ((sp - 48).toNat + 24) 4 4 $$ [P0 P4]
                · iframe P0 P4
                ihave T24b := stk_join n ((sp - 48).toNat + 24) 8 16 $$ [P8 T16b]
                · iframe P8 T16b
                ihave S48 := stk_join n (sp - 48).toNat 24 24 $$ [T24 T24b]
                · iframe T24 T24b
                ihave T144 := stk_addr (show (sp - 48).toNat - 144 = sp.toNat - 192 by omega) $$ T144
                ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                iapply stk_join n (sp.toNat - 192) 144 48
                iframe T144 S48
              iunfold resStr
              rw [hres]
              iunfold errStr
              iexists q, p1, cap1, j', hl1, F1, acc ++ body
              isplitr
              · ipureintro; exact ⟨hq, hj', by omega⟩
              rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop],
                show out.toNat + 4 + 4 = out.toNat + 8 by omega]
              iframe O0 O4 O8 Hrd S0 S4 S8 HE'
            | some pr =>
              -- the escape decodes: back to the loop's head
              obtain ⟨eo, m⟩ := pr
              simp only [res649, hrest, he]
              icases HQ with ⟨%hrs, Hrd, %p2, %hl2, %hhl2, S0, S4, S8, Hsb⟩
              subst hrs
              obtain ⟨heo1, heom, hml⟩ := escDecode_len rest eo m he
              have hrl2 : rest.length = bs.length - (k + 1) := by rw [← hrest]; simp
              have hdr : bs.drop (k + 1 + m) = rest.drop m := by rw [← hrest, List.drop_drop]
              have hl2le := hlAfter_le _ _ _ _ _ hhl2
              have hkeo : escK rest = eo.length := by simp [ParseEscape.escK, he]
              rw [hkeo] at hroom3
              have hroom4 := hroom3.2 hl2 hhl2 eo m he
              have hrun' : strRun (bs.drop (k + 1 + m)) (acc ++ body ++ eo) = strRun (bs.drop i) [] := by
                rw [hdr, ← hrun, strRun_cons (bs.drop j) acc 0x5C rest (by rw [htail, htx]), hbody]
                simp [he]
              have hnb : ¬ borrowed (bs.drop i) := by
                by_cases hji : j = i
                · subst hji; unfold borrowed; rw [htail, htx]; simp
                · exact hjb hji
              mstep; mstep
              iapply mwpi_cons
              iapply mwpi_br_if_taken'
              isplitr
              · ipureintro; exact ⟨rfl, by decide⟩
              mctrl_norm
              (try simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil])
              iapply pure_pay_intro'
              isplitl [Hc]
              · iexact Hc
              isplitr
              · ipureintro; exact ⟨by simp, by omega⟩
              inext
              iintro Hc
              iunfold rd, sliceRead at Hrd
              icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
              try rw [← List.append_assoc acc body eo]
              iexists k + 1 + m, acc ++ body ++ eo, p2, capAfter cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat eo.length),
                hl2, fAfter F1 cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat eo.length), _, _, _, _, _, _
              isplitr
              · ipureintro
                have hcap2 := capAfter_le cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat eo.length) (by omega)
                  (by simp; omega)
                refine ⟨by first | rfl | trivial, by first | rfl | trivial, by omega, by omega, hrun',
                  fun h => absurd (congrArg List.length h) (by simp only [List.length_append, List.length_nil]; omega),
                  fun h => absurd h (by omega),
                  fun _ => hnb, by simp; omega, ?_, by omega, by rw [hdr]; exact hroom4⟩
                simp at hcap2 ⊢; omega
              iframe Ho He Hw Ht Hvt Hg D0 D4 D8 Hb S0 S4 Hsb
              isplitl [Hc]
              · iapply BorrowMut.credits_le
                iframe Hc
                ipureintro
                simp only [he] at hcb
                rw [hdr]
                omega
              isplitr [S8]
              · ihave P0 := stk_word n ((sp - 48).toNat + 24) _ $$ P0
                ihave P4 := stk_word n ((sp - 48).toNat + 28) _ $$ P4
                ihave P8 := stk_join n ((sp - 48).toNat + 24) 4 4 $$ [P0 P4]
                · iframe P0 P4
                ihave T24b := stk_join n ((sp - 48).toNat + 24) 8 16 $$ [P8 T16b]
                · iframe P8 T16b
                ihave S48 := stk_join n (sp - 48).toNat 24 24 $$ [T24 T24b]
                · iframe T24 T24b
                ihave T144 := stk_addr (show (sp - 48).toNat - 144 = sp.toNat - 192 by omega) $$ T144
                ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                iapply stk_join n (sp.toNat - 192) 144 48
                iframe T144 S48
              rw [show UInt32.ofNat ((acc ++ body).length + eo.length) = UInt32.ofNat (acc ++ body ++ eo).length by simp only [List.length_append]]
              iexact S8
          have h92 : Numeric.bool (Numeric.irelop32 IRelOp.eq x.toUInt32 92) = 0 := by rw [eq92, if_neg hx92]
          brn h92
          by_cases hx34 : x.toNat = 34
          · -- `"`: the end of the string
            have hx : x = 0x22 := UInt8.toNat_inj.mp (by rw [hx34]; rfl)
            subst hx
            have hres : strRun (bs.drop i) [] = .ok (acc ++ body) rest := by
              rw [← hrun, strRun_cons _ _ 0x22 rest (by rw [htail, htx]), hbody]; simp
            have hcb := costRun_stop cfg F' cap acc (bs.drop j) bs.length (by
              intro r; rw [htail, htx]; simp)
            unfold costBase at hcb
            rw [hbody, Nat.add_mul (500 + 30 * body.length)] at hcb
            have hrl : bs.length - rest.length = k + 1 := by rw [htx] at htl; simp at htl; omega
            icases stk_split n (sp.toNat - 192) 144 48 $$ Hs with ⟨T144, T48⟩
            rw [show sp.toNat - 192 + 144 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 8 40 $$ T48 with ⟨T8, T40⟩
            icases stk_split n ((sp - 48).toNat + 8) 24 16 $$ T40 with ⟨T24, T16⟩
            icases stk_split n ((sp - 48).toNat + 8 + 24) 12 4 $$ T16 with ⟨T12, T4⟩
            iunfold stk at T8 T12
            icases T8 with ⟨%s8, %hs8, T8⟩
            icases T12 with ⟨%s12, %hs12, T12⟩
            mstep; mstep; mstep
            brn (by decide)
            mstep; mstep
            mstep [S8]
            by_cases hae : acc = []
            · -- no escape: the slice is borrowed
              obtain ⟨hji, hp, hcap', hhl', hF'⟩ := hacc0 hae
              subst hp hcap' hhl' hF' hae hji
              have hbor : borrowed (bs.drop j) := by unfold borrowed; rw [htail, htx]; rfl
              simp only [List.length_nil, List.nil_append, Nat.zero_add] at hres hcb hcr ⊢
              brn rfl
              mstep; mstep; mstep; mstep; mstep; mstep
              mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48) (UInt32.ofNat j)
                (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062248 s8 hs8 (by omega)
                (by simp; omega) (by simp; omega)) using [T8]
              · iframe T8
              icases HQ with ⟨%hrs, P0, P4⟩
              subst hrs
              mcredits (300 * cfg.regularOpCost + (Z + Rl))
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
              rw [show UInt32.ofNat k - UInt32.ofNat j = UInt32.ofNat body.length by
                apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
              mstep; mstep; mstep; mstep; mstep; mstep
              have h32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
              have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
              have hsplit' : bs.drop j = body ++ 0x22 :: rest := by rw [hsplit, htx]
              by_cases hutf : Utf8.utf8Ok body = true
              · -- `Ok(Borrowed)`
                ihave Hb := U128From.memBytes_split n ptr.toNat j bs (by omega) $$ Hb
                icases Hb with ⟨B0, Bd⟩
                rw [hsplit']
                ihave Bd := U128From.memBytes_split n (ptr.toNat + j) body.length (body ++ 0x22 :: rest) (by simp) $$ Bd
                icases Bd with ⟨Bbody, Brest⟩
                rw [List.take_left' rfl, List.drop_left' rfl]
                ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + j = (ptr + UInt32.ofNat j).toNat by
                  simp [UInt32.toNat_add]; omega) $$ Bbody
                ihave T12 := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                  rw [UInt32.toNat_add, h48]; simp; omega) $$ T12
                icases stk_split n (sp.toNat - 192) 112 32 $$ T144 with ⟨T112, T32⟩
                ihave T32 := stk_addr (show sp.toNat - 192 + 112 = (sp - 48).toNat - 32 by omega) $$ T32
                have hK3 : (12 + cost648 (UInt32.ofNat body.length).toNat) * cfg.regularOpCost =
                    52 * cfg.regularOpCost + cost927 body.length * cfg.regularOpCost := by
                  rw [hm32]; unfold cost648; simp only [Nat.add_mul]; omega
                rw [show Z + Rl = cost927 body.length * cfg.regularOpCost +
                  (Z - cost927 body.length * cfg.regularOpCost + Rl) by omega]
                mcall (f648_spec_valid cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg (A 927) ha927 (by omega) Cg gt
                  (sp - 48) (sp - 48 + 32) de (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) s12 body hs12
                  (by rw [UInt32.toNat_add, h48]; simp; omega) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
                  (by omega) hutf) using [Hg T32 T12 Bbody Hw]
                · iframe Hg T32 T12 Bbody Hw
                rw [hK3]
                mcredits (60 * cfg.regularOpCost + (Z - cost927 body.length * cfg.regularOpCost + Rl))
                icases HQ with ⟨%hrs, Hg, T32, Q0, Q4, Q8, Bbody, Hw⟩
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
                iframe Hg Hvt He Hw Ht
                isplitr [O0 O4 O8 O12 D0 D4 D8 B0 Bbody Brest S0 S4 S8 Hsb]
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
                  ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [P8 T24]
                  · iframe P8 T24
                  ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                  · iframe S32' Q12
                  ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 T4]
                  · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 T4
                  ihave S80' := stk_join n ((sp - 48).toNat - 32) 32 48 $$ [T32 S48]
                  · rw [show (sp - 48).toNat - 32 + 32 = (sp - 48).toNat by omega]; iframe T32 S48
                  ihave S80' := stk_addr (show (sp - 48).toNat - 32 = sp.toNat - 192 + 112 by omega) $$ S80'
                  iapply stk_join n (sp.toNat - 192) 112 80
                  iframe T112 S80'
                iunfold resStr
                rw [hres]
                simp only [if_pos hutf, if_pos hbor]
                rw [hrl]
                rw [show out.toNat + 4 + 4 + 4 = out.toNat + 12 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
                iframe O0 O4 O8 O12 S0 S4 S8 Hsb
                iunfold rd, sliceRead
                rw [show (k + 1) = k + 1 from rfl]
                iframe D0 D4 D8
                ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                  simp [UInt32.toNat_add]; omega) $$ Bbody
                ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (34 :: rest) rfl $$ [Bbody Brest]
                · iframe Bbody Brest
                rw [← hsplit']
                ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
                · iframe B0 Bd
                rw [List.take_append_drop]
                iexact Bb
              · -- the body is not UTF-8: `as_str` fails (657)
                have hbad : Utf8.utf8Ok body = false := by simpa using hutf
                icases U128From.memBytes_split n ((sp - 48).toNat + 8 + 24) 8 s12 (by omega) $$ T12 with ⟨T12a, T12b⟩
                ihave T12a := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                  rw [UInt32.toNat_add, h48]; simp; omega) $$ T12a
                ihave Hrd : rd n de ptr bs (k + 1) $$ [D0 D4 D8 Hb]
                · iunfold rd, sliceRead; iframe D0 D4 D8 Hb
                icases stk_split n (sp.toNat - 192) 32 112 $$ T144 with ⟨T32a, T112⟩
                ihave T112 := stk_addr (show sp.toNat - 192 + 32 = (sp - 48).toNat - 112 by omega) $$ T112
                icases ParseEscape.sbuf_split $$ Hsb with ⟨Hinv, Hw'⟩
                have hr4 := ((roomRun_unfold maxP hl' cap [] (bs.drop j)).mp hroomj).1
                have key := f648_spec_bad (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
                  (sp - 48) (sp - 48 + 32) de ptr (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) idx (s12.take 8) bs
                  (k + 1) j maxP hl' (if cap = 0 then live else (p.toNat, cap.toNat) :: live) F' (by simp; omega)
                  (by rw [h32]; omega) hde (by omega) (by omega) hptr
                  (by simp [UInt32.toNat_add]; omega) (by rw [hm32]; omega)
                  (by rw [hm32, hsplit, List.take_left' rfl]; exact hbad) (by omega) hr4
                rw [hm32] at key
                have hK60 : (60 + cost927 body.length) * cfg.regularOpCost =
                    60 * cfg.regularOpCost + cost927 body.length * cfg.regularOpCost := Nat.add_mul _ _ _
                unfold errCode at key
                have hEk := costErr_monoF cfg F' (F' + 2) (k + 1) (by omega)
                have hEk2 := costErr_mono cfg (F' + 2) (k + 1) (bs.length + 1) (by omega)
                rw [show Z + Rl = cost927 body.length * cfg.regularOpCost + costErr cfg F' (k + 1) +
                  (Z - cost927 body.length * cfg.regularOpCost - costErr cfg F' (k + 1) + Rl) by omega]
                mcall key using [Hg T112 Hvt Hinv T12a Hrd Hw]
                · iframe Hg T112 Hvt Hinv T12a Hrd Hw
                clear key
                mcredits (30 * cfg.regularOpCost + Rl)
                icases HQ with ⟨%hrs, %q, %hq, Hg, T112, Hvt, HA, Q0, Q4, Hrd, Hw⟩
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
                iframe Hg Hvt He Hw Ht
                isplitr [HA O0 O4 O8 Hrd S0 S4 S8 Hw']
                · ihave P0 := stk_word n (sp - 48).toNat _ $$ P0
                  ihave P4 := stk_word n ((sp - 48).toNat + 4) _ $$ P4
                  ihave P8 := stk_join n (sp - 48).toNat 4 4 $$ [P0 P4]
                  · iframe P0 P4
                  ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
                  ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
                  ihave Q8 := stk_join n ((sp - 48).toNat + 32) 4 4 $$ [Q0 Q4]
                  · iframe Q0 Q4
                  ihave T12b := stk_intro n _ _ $$ T12b
                  rw [show (s12.drop 8).length = 4 by simp; omega]
                  ihave T12b := stk_addr (show (sp - 48).toNat + 8 + 24 + 8 = (sp - 48).toNat + 32 + 8 by omega) $$ T12b
                  ihave Q12 := stk_join n ((sp - 48).toNat + 32) 8 4 $$ [Q8 T12b]
                  · iframe Q8 T12b
                  ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [P8 T24]
                  · iframe P8 T24
                  ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                  · iframe S32' Q12
                  ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 T4]
                  · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 T4
                  ihave T112 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 192 + 32 by omega) $$ T112
                  ihave T144 := stk_join n (sp.toNat - 192) 32 112 $$ [T32a T112]
                  · iframe T32a T112
                  ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                  iapply stk_join n (sp.toNat - 192) 144 48
                  iframe T144 S48
                iunfold resStr
                rw [hres]
                simp only [hbad, Bool.false_eq_true, ite_false]
                iunfold errStr
                iexists q, p, cap, k + 1, hl', F', []
                isplitr
                · ipureintro; exact ⟨hq, by omega, hhl⟩
                rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop],
                  show out.toNat + 4 + 4 = out.toNat + 8 by omega]
                iframe O0 O4 O8 Hrd S0 S4 S8
                iapply ParseEscape.sbufE_intro
                iframe HA Hw'
            · -- the scratch holds the escapes' bytes: append the rest, `Ok(Copied)`
              have hji : j ≠ i := fun e => hae (hj0 e)
              have hnb := hjb hji
              have hal : 0 < acc.length := List.length_pos_iff.mpr hae
              have hlenu : (UInt32.ofNat acc.length) ≠ 0 := fun e => by
                have := congrArg UInt32.toNat e; simp at this; omega
              iapply mwpi_cons
              iapply mwpi_br_if_taken'
              isplitr
              · ipureintro; exact ⟨rfl, hlenu⟩
              mctrl_norm
              repeat mpay
              icases stk_split n ((sp - 48).toNat + 8) 8 16 $$ T24 with ⟨T8b, T16⟩
              icases stk_split n ((sp - 48).toNat + 8 + 8) 8 8 $$ T16 with ⟨T8c, T8d⟩
              iunfold stk at T8b T8c
              icases T8b with ⟨%u8, %hu8, T8b⟩
              icases T8c with ⟨%v8, %hv8, T8c⟩
              ihave T8c := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 8 = (sp - 48 + 16).toNat by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ T8c
              mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
              mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48 + 16) (UInt32.ofNat j)
                (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062280 v8 hv8 (by rw [UInt32.toNat_add, h48]; simp; omega)
                (by simp; omega) (by simp; omega)) using [T8c]
              · iframe T8c
              icases HQ with ⟨%hrs, P0, P4⟩
              subst hrs
              mcredits (300 * cfg.regularOpCost + (Z + Rl))
              ihave P0 := AllocNewCell.memBytes_addr (show (sp - 48 + 16).toNat = (sp - 48).toNat + 16 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ P0
              ihave P4 := AllocNewCell.memBytes_addr (show (sp - 48 + 16).toNat + 4 = (sp - 48).toNat + 20 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ P4
              rw [show UInt32.ofNat k - UInt32.ofNat j = UInt32.ofNat body.length by
                apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
              mstep; mstep; mstep [P0]; mstep; mstep [P4]
              -- the body's bytes, for 613
              have hsplit' : bs.drop j = body ++ 0x22 :: rest := by rw [hsplit, htx]
              have hab : (acc ++ body).length = acc.length + body.length := List.length_append
              ihave Hb := U128From.memBytes_split n ptr.toNat j bs (by omega) $$ Hb
              icases Hb with ⟨B0, Bd⟩
              rw [hsplit']
              ihave Bd := U128From.memBytes_split n (ptr.toNat + j) body.length (body ++ 0x22 :: rest) (by simp) $$ Bd
              icases Bd with ⟨Bbody, Brest⟩
              rw [List.take_left' rfl, List.drop_left' rfl]
              ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + j = (ptr + UInt32.ofNat j).toNat by
                simp [UInt32.toNat_add]; omega) $$ Bbody
              icases stk_split n (sp.toNat - 192) 32 112 $$ T144 with ⟨T32a, T112⟩
              ihave T112 := stk_addr (show sp.toNat - 192 + 32 = (sp - 48).toNat - 112 by omega) $$ T112
              have hroom1 := (roomRun_unfold maxP hl' cap acc (bs.drop j)).mp hroomj
              rw [hbody] at hroom1
              have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
              have hcapl : cap.toNat < 2 ^ 27 := by omega
              have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
                (sp - 48) sc (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) p cap idx maxP hl' live F' acc body
                (by omega) (by omega) hcapl (by rw [hm32]; omega) hm32.symm (by simp [UInt32.toNat_add]; omega) hroom1.2.1
              rw [show Z + Rl = costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) +
                (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl) by omega]
              mcall key using [Hg T112 Hvt S0 S4 S8 Hsb Bbody]
              · iframe Hg T112 Hvt S0 S4 S8 Hsb Bbody
              clear key
              icases HQ with ⟨%hrs, %p1, %hl1, %hhl1, Hg, T112, Hvt, S0, S4, S8, Hsb, Bbody⟩
              subst hrs
              rw [hm32]
              generalize hcap1 : capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = cap1
              generalize hF1 : fAfter F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = F1
              have hl1le := hlAfter_le _ _ _ _ _ hhl1
              mcredits (200 * cfg.regularOpCost + (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl))
              mstep; mstep
              mstep; mstep [D8]
              mstep; mstep; mstep; mstep; mstep; mstep
              rw [SerdeRead.ofNat_succ k (by omega)]
              have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (k + 1)) (UInt32.ofNat k)) = 0 := by
                rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
              brn hov
              clear hov
              mstep; mstep; mstep [D8]
              ihave T8b := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 = (sp - 48 + 8).toNat by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ T8b
              mstep; mstep; mstep; mstep
              mcall (f728_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (sp - 48 + 8) sc p1
                (UInt32.ofNat (acc.length + body.length)) u8 hu8) using [T8b S0 S8]
              · iframe T8b S0 S8
              icases HQ with ⟨%hrs, R0, R4, S0, S8⟩
              subst hrs
              ihave R0 := AllocNewCell.memBytes_addr (show (sp - 48 + 8).toNat = (sp - 48).toNat + 8 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ R0
              ihave R4 := AllocNewCell.memBytes_addr (show (sp - 48 + 8).toNat + 4 = (sp - 48).toNat + 12 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ R4
              mstep; mstep; mstep; mstep; mstep; mstep [R0]; mstep; mstep [R4]
              have h32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
              have hm2 : (UInt32.ofNat (acc.length + body.length)).toNat = (acc ++ body).length := by simp; omega
              have hres' : strRun (bs.drop i) [] = .ok (acc ++ body) rest := hres
              by_cases hutf : Utf8.utf8Ok (acc ++ body) = true
              · -- `Ok(Copied)`
                ihave T12 := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                  rw [UInt32.toNat_add, h48]; simp; omega) $$ T12
                icases sbuf_bytes $$ Hsb with ⟨%hpb, Bs, Hsw⟩
                icases stk_split n ((sp - 48).toNat - 112) 80 32 $$ T112 with ⟨T80, T32⟩
                ihave T32 := stk_addr (show (sp - 48).toNat - 112 + 80 = (sp - 48).toNat - 32 by omega) $$ T32
                have hK3 : (12 + cost648 (UInt32.ofNat (acc.length + body.length)).toNat) * cfg.regularOpCost =
                    52 * cfg.regularOpCost + cost927 (acc.length + body.length) * cfg.regularOpCost := by
                  rw [hm2]; unfold cost648; simp only [Nat.add_mul, List.length_append]; omega
                rw [show Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl =
                  cost927 (acc.length + body.length) * cfg.regularOpCost +
                  (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                    cost927 (acc.length + body.length) * cfg.regularOpCost + Rl) by omega]
                mcall (f648_spec_valid cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg (A 927) ha927 (by omega) Cg gt
                  (sp - 48) (sp - 48 + 32) de p1 (UInt32.ofNat (acc.length + body.length)) s12 (acc ++ body) hs12
                  (by rw [h32]; omega) hm2.symm (by rw [hm2]; omega) (by omega) hutf) using [Hg T32 T12 Bs Hw]
                · iframe Hg T32 T12 Bs Hw
                rw [hK3]
                mcredits (60 * cfg.regularOpCost + Rl)
                icases HQ with ⟨%hrs, Hg, T32, Q0, Q4, Q8, Bs, Hw⟩
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
                iframe Hg Hvt He Hw Ht
                isplitr [O0 O4 O8 O12 D0 D4 D8 B0 Bbody Brest S0 S4 S8 Hsw Bs]
                · ihave P0 := stk_word n ((sp - 48).toNat + 16) _ $$ P0
                  ihave P4 := stk_word n ((sp - 48).toNat + 20) _ $$ P4
                  ihave R0 := stk_word n ((sp - 48).toNat + 8) _ $$ R0
                  ihave R4 := stk_word n ((sp - 48).toNat + 12) _ $$ R4
                  ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
                  ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
                  ihave Q8 := stk_word n ((sp - 48).toNat + 32 + 8) _ $$ Q8
                  ihave R8 := stk_join n ((sp - 48).toNat + 8) 4 4 $$ [R0 R4]
                  · iframe R0 R4
                  ihave P8 := stk_join n ((sp - 48).toNat + 16) 4 4 $$ [P0 P4]
                  · iframe P0 P4
                  ihave T16 := stk_join n ((sp - 48).toNat + 8 + 8) 8 8 $$ [P8 T8d]
                  · rw [show (sp - 48).toNat + 8 + 8 = (sp - 48).toNat + 16 by omega]; iframe P8 T8d
                  ihave T24 := stk_join n ((sp - 48).toNat + 8) 8 16 $$ [R8 T16]
                  · iframe R8 T16
                  ihave Q48 := stk_join n ((sp - 48).toNat + 32 + 4) 4 4 $$ [Q4 Q8]
                  · rw [show (sp - 48).toNat + 32 + 4 + 4 = (sp - 48).toNat + 32 + 8 by omega]; iframe Q4 Q8
                  ihave Q12 := stk_join n ((sp - 48).toNat + 32) 4 8 $$ [Q0 Q48]
                  · iframe Q0 Q48
                  ihave T8 := stk_intro n _ _ $$ T8
                  rw [hs8]
                  ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [T8 T24]
                  · iframe T8 T24
                  ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                  · iframe S32' Q12
                  ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 T4]
                  · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 T4
                  ihave T32 := stk_addr (show (sp - 48).toNat - 32 = (sp - 48).toNat - 112 + 80 by omega) $$ T32
                  ihave T112 := stk_join n ((sp - 48).toNat - 112) 80 32 $$ [T80 T32]
                  · iframe T80 T32
                  ihave T112 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 192 + 32 by omega) $$ T112
                  ihave T144 := stk_join n (sp.toNat - 192) 32 112 $$ [T32a T112]
                  · iframe T32a T112
                  ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                  iapply stk_join n (sp.toNat - 192) 144 48
                  iframe T144 S48
                iunfold resStr
                rw [hres']
                simp only [if_pos hutf, if_neg hnb]
                rw [hrl]
                rw [show out.toNat + 4 + 4 + 4 = out.toNat + 12 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
                rw [show UInt32.ofNat (acc.length + body.length) = UInt32.ofNat (acc ++ body).length by simp]
                iframe O0 O12
                isplitr [O4 O8 S0 S4 S8 Hsw Bs]
                · iunfold rd, sliceRead
                  iframe D0 D4 D8
                  ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                    simp [UInt32.toNat_add]; omega) $$ Bbody
                  ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (34 :: rest) rfl $$ [Bbody Brest]
                  · iframe Bbody Brest
                  rw [← hsplit']
                  ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
                  · iframe B0 Bd
                  rw [List.take_append_drop]
                  iexact Bb
                iexists p1, cap1, hl1, F1
                isplitr
                · ipureintro; omega
                iframe O4 O8 S0 S4 S8
                iapply Hsw $$ Bs
              · -- not UTF-8: `as_str` fails (657)
                have hbad : Utf8.utf8Ok (acc ++ body) = false := by simpa using hutf
                icases U128From.memBytes_split n ((sp - 48).toNat + 8 + 24) 8 s12 (by omega) $$ T12 with ⟨T12a, T12b⟩
                ihave T12a := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                  rw [UInt32.toNat_add, h48]; simp; omega) $$ T12a
                ihave Hrd : rd n de ptr bs (k + 1) $$ [D0 D4 D8 B0 Bbody Brest]
                · iunfold rd, sliceRead
                  iframe D0 D4 D8
                  ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                    simp [UInt32.toNat_add]; omega) $$ Bbody
                  ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (34 :: rest) rfl $$ [Bbody Brest]
                  · iframe Bbody Brest
                  rw [← hsplit']
                  ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
                  · iframe B0 Bd
                  rw [List.take_append_drop]
                  iexact Bb
                icases ParseEscape.sbuf_split $$ Hsb with ⟨Hinv, Hw'⟩
                icases sbufR_bytes $$ Hw' with ⟨%hpb, Bs, Hw'⟩
                have hr4 := (hroom1.2.2 hl1 hhl1).1
                have key := SerdeErrBox.f648_spec_bad_mem (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm
                  (by omega) Cg gt (sp - 48) (sp - 48 + 32) de ptr p1 (UInt32.ofNat (acc.length + body.length)) idx
                  (s12.take 8) bs (acc ++ body) (k + 1) maxP hl1 (if cap1 = 0 then live else (p1.toNat, cap1.toNat) :: live)
                  F1 (by simp; omega) (by rw [h32]; omega) hde (by omega) (by omega) hptr hm2.symm (by rw [hm2]; omega)
                  hbad (by omega) hr4
                rw [hm2] at key
                have hK60 : (60 + cost927 (acc ++ body).length) * cfg.regularOpCost =
                    60 * cfg.regularOpCost + cost927 (acc ++ body).length * cfg.regularOpCost := Nat.add_mul _ _ _
                unfold errCode at key
                have hF1le : F1 ≤ F' + 2 := by rw [← hF1]; unfold fAfter; split <;> omega
                have hEk := costErr_monoF cfg F1 (F' + 2) (k + 1) hF1le
                have hEk2 := costErr_mono cfg (F' + 2) (k + 1) (bs.length + 1) (by omega)
                rw [show Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl =
                  cost927 (acc ++ body).length * cfg.regularOpCost + costErr cfg F1 (k + 1) +
                  (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                    cost927 (acc ++ body).length * cfg.regularOpCost - costErr cfg F1 (k + 1) + Rl) by
                  simp only [List.length_append]; omega]
                mcall key using [Hg T112 Hvt Hinv T12a Hrd Bs Hw]
                · iframe Hg T112 Hvt Hinv T12a Hrd Bs Hw
                clear key
                mcredits (30 * cfg.regularOpCost + Rl)
                icases HQ with ⟨%hrs, %q, %hq, Hg, T112, Hvt, HA, Q0, Q4, Hrd, Bs, Hw⟩
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
                iframe Hg Hvt He Hw Ht
                isplitr [HA O0 O4 O8 Hrd S0 S4 S8 Hw' Bs]
                · ihave P0 := stk_word n ((sp - 48).toNat + 16) _ $$ P0
                  ihave P4 := stk_word n ((sp - 48).toNat + 20) _ $$ P4
                  ihave R0 := stk_word n ((sp - 48).toNat + 8) _ $$ R0
                  ihave R4 := stk_word n ((sp - 48).toNat + 12) _ $$ R4
                  ihave R8 := stk_join n ((sp - 48).toNat + 8) 4 4 $$ [R0 R4]
                  · iframe R0 R4
                  ihave P8 := stk_join n ((sp - 48).toNat + 16) 4 4 $$ [P0 P4]
                  · iframe P0 P4
                  ihave T16 := stk_join n ((sp - 48).toNat + 8 + 8) 8 8 $$ [P8 T8d]
                  · rw [show (sp - 48).toNat + 8 + 8 = (sp - 48).toNat + 16 by omega]; iframe P8 T8d
                  ihave T24 := stk_join n ((sp - 48).toNat + 8) 8 16 $$ [R8 T16]
                  · iframe R8 T16
                  ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
                  ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
                  ihave Q8 := stk_join n ((sp - 48).toNat + 32) 4 4 $$ [Q0 Q4]
                  · iframe Q0 Q4
                  ihave T12b := stk_intro n _ _ $$ T12b
                  rw [show (s12.drop 8).length = 4 by simp; omega]
                  ihave T12b := stk_addr (show (sp - 48).toNat + 8 + 24 + 8 = (sp - 48).toNat + 32 + 8 by omega) $$ T12b
                  ihave Q12 := stk_join n ((sp - 48).toNat + 32) 8 4 $$ [Q8 T12b]
                  · iframe Q8 T12b
                  ihave T8 := stk_intro n _ _ $$ T8
                  rw [hs8]
                  ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [T8 T24]
                  · iframe T8 T24
                  ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                  · iframe S32' Q12
                  ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 T4]
                  · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 T4
                  ihave T112 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 192 + 32 by omega) $$ T112
                  ihave T144 := stk_join n (sp.toNat - 192) 32 112 $$ [T32a T112]
                  · iframe T32a T112
                  ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                  iapply stk_join n (sp.toNat - 192) 144 48
                  iframe T144 S48
                iunfold resStr
                rw [hres']
                simp only [hbad, Bool.false_eq_true, ite_false]
                iunfold errStr
                iexists q, p1, cap1, k + 1, hl1, F1, acc ++ body
                isplitr
                · ipureintro; exact ⟨hq, by omega, by omega⟩
                rw [show (ob.drop 4).drop 4 = ob.drop 8 by simp [List.drop_drop],
                  show out.toNat + 4 + 4 = out.toNat + 8 by omega]
                rw [show UInt32.ofNat (acc.length + body.length) = UInt32.ofNat (acc ++ body).length by simp]
                iframe O0 O4 O8 Hrd S0 S4 S8
                iapply ParseEscape.sbufE_intro
                iframe HA
                iapply Hw' $$ Bs
          · -- a control byte: `ControlCharacterWhileParsingString`
            have hx22 : x ≠ 0x22 := fun e => hx34 (by rw [e]; rfl)
            have hx5c : x ≠ 0x5C := fun e => hx92 (by rw [e]; rfl)
            have hres : strRun (bs.drop i) [] = .ctrl := by
              rw [← hrun, strRun_cons _ _ x rest (by rw [htail, htx])]; simp [hx22, hx5c]
            have hcb := costRun_stop cfg F' cap acc (bs.drop j) bs.length (by
              intro r; rw [htail, htx]; simp; intro e; exact absurd e hx5c)
            unfold costBase at hcb
            rw [hbody, Nat.add_mul (500 + 30 * body.length)] at hcb
            have hEk := costErr_monoF cfg F' (F' + 2) (k + 1) (by omega)
            have hEk2 := costErr_mono cfg (F' + 2) (k + 1) (bs.length + 1) (by omega)
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
            icases stk_split n (sp.toNat - 192) 144 48 $$ Hs with ⟨S144, S48⟩
            icases stk_split n (sp.toNat - 192) 64 80 $$ S144 with ⟨S64, S80⟩
            rw [show sp.toNat - 192 + 144 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 32 16 $$ S48 with ⟨SF, S16⟩
            icases stk_split n ((sp - 48).toNat + 32) 4 12 $$ S16 with ⟨SC0, S12⟩
            icases stk_split n ((sp - 48).toNat + 32 + 4) 8 4 $$ S12 with ⟨SC8, S4'⟩
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
            ihave S80 := stk_addr (show sp.toNat - 192 + 64 = (sp - 48).toNat - 80 by omega) $$ S80
            icases U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨O8, O16⟩
            icases ParseEscape.sbuf_split $$ Hsb with ⟨Hinv, Hw'⟩
            have hr4 := ((roomRun_unfold maxP hl' cap acc (bs.drop j)).mp hroomj).1
            have key := f647_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
              (sp - 48) out de (sp - 48 + 32) ptr idx (ob.take 8) (bytes32 15 ++ sc8) bs (k + 1) maxP hl'
              (if cap = 0 then live else (p.toNat, cap.toNat) :: live) F'
              (by simp; omega) (by omega) (by simp; omega) (by rw [UInt32.toNat_add, h48]; simp; omega) hde (by omega)
              (by omega) hptr (by omega) hr4
            unfold errCode at key
            have key2 := key.trans (AllocGen.MFunSpec_cost (K' := fun _ => Z) (fun _ => by omega))
            clear key
            mcall key2 using [Hg S80 Hvt Hinv O8 C D0 D4 D8 Hb]
            · iframe Hg S80 Hvt Hinv O8 C
              iunfold rd, sliceRead
              iframe D0 D4 D8 Hb
            clear key2
            mcredits (20 * cfg.regularOpCost + Rl)
            icases HQ with ⟨%hrs, %q, %hq, Hg, S80, Hvt, HA, O0, O4, C, Hrd⟩
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
            iframe Hg Hvt He Hw Ht
            isplitr [HA O0 O4 O16 Hrd S0 S4 S8 Hw']
            · ihave C := stk_intro n _ _ $$ C
              rw [show (bytes32 15 ++ sc8).length = 12 by simp; omega]
              ihave C := stk_addr (show (sp - 48 + 32).toNat = (sp - 48).toNat + 32 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ C
              ihave J1 := stk_join n ((sp - 48).toNat + 32) 12 4 $$ [C S4']
              · rw [show (sp - 48).toNat + 32 + 12 = (sp - 48).toNat + 32 + 4 + 8 by omega]; iframe C S4'
              ihave J2 := stk_join n (sp - 48).toNat 32 16 $$ [SF J1]
              · iframe SF J1
              ihave S80 := stk_addr (show (sp - 48).toNat - 80 = sp.toNat - 192 + 64 by omega) $$ S80
              ihave J3 := stk_join n (sp.toNat - 192) 64 80 $$ [S64 S80]
              · iframe S64 S80
              ihave J2 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ J2
              iapply stk_join n (sp.toNat - 192) 144 48
              iframe J3 J2
            iunfold resStr
            rw [hres]
            iunfold errStr
            iexists q, p, cap, k + 1, hl', F', acc
            isplitr
            · ipureintro; exact ⟨hq, by omega, hhl⟩
            iframe O0 O4 O16 Hrd S0 S4 S8
            iapply ParseEscape.sbufE_intro
            iframe HA Hw'
      · -- EOF: the scan reaches the end of the input
        have hk : k = bs.length := by omega
        have htn : tail = [] := by rw [← List.length_eq_zero_iff]; omega
        have hres : strRun (bs.drop i) [] = .eof := by rw [← hrun, strRun_nil _ _ (by rw [htail, htn])]
        have hcb := costRun_stop cfg F' cap acc (bs.drop j) bs.length (by intro r; rw [htail, htn]; simp)
        unfold costBase at hcb
        rw [hbody, Nat.add_mul (500 + 30 * body.length)] at hcb
        have hEk := costErr_monoF cfg F' (F' + 2) bs.length (by omega)
        have hEk2 := costErr_mono cfg (F' + 2) bs.length (bs.length + 1) (by omega)
        subst hk
        rw [show 30 * (j + body.length - bs.length) * cfg.regularOpCost = 0 by
          rw [show j + body.length - bs.length = 0 by omega]; simp, Nat.zero_add]
        have heq : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat bs.length) (UInt32.ofNat bs.length)) ≠ 0 := by
          simp [Numeric.bool, Numeric.irelop32]
        have hlu : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat bs.length) (UInt32.ofNat j)) = 0 := by
          simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
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
        icases stk_split n (sp.toNat - 192) 144 48 $$ Hs with ⟨S144, S48⟩
        icases stk_split n (sp.toNat - 192) 64 80 $$ S144 with ⟨S64, S80⟩
        rw [show sp.toNat - 192 + 144 = (sp - 48).toNat by omega]
        icases stk_split n (sp - 48).toNat 32 16 $$ S48 with ⟨SF, S16⟩
        icases stk_split n ((sp - 48).toNat + 32) 4 12 $$ S16 with ⟨SC0, S12⟩
        icases stk_split n ((sp - 48).toNat + 32 + 4) 8 4 $$ S12 with ⟨SC8, S4'⟩
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
        ihave S80 := stk_addr (show sp.toNat - 192 + 64 = (sp - 48).toNat - 80 by omega) $$ S80
        icases U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨O8, O16⟩
        icases ParseEscape.sbuf_split $$ Hsb with ⟨Hinv, Hw'⟩
        have hr4 := ((roomRun_unfold maxP hl' cap acc (bs.drop j)).mp hroomj).1
        have key := f647_spec (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
          (sp - 48) out de (sp - 48 + 32) ptr idx (ob.take 8) (bytes32 4 ++ sc8) bs bs.length maxP hl'
          (if cap = 0 then live else (p.toNat, cap.toNat) :: live) F'
          (by simp; omega) (by omega) (by simp; omega) (by rw [UInt32.toNat_add, h48]; simp; omega) hde le_rfl
          (by omega) hptr (by omega) hr4
        unfold errCode at key
        have key2 := key.trans (AllocGen.MFunSpec_cost (K' := fun _ => Z) (fun _ => by omega))
        clear key
        mcall key2 using [Hg S80 Hvt Hinv O8 C D0 D4 D8 Hb]
        · iframe Hg S80 Hvt Hinv O8 C
          iunfold rd, sliceRead
          iframe D0 D4 D8 Hb
        clear key2
        mcredits (20 * cfg.regularOpCost + Rl)
        icases HQ with ⟨%hrs, %q, %hq, Hg, S80, Hvt, HA, O0, O4, C, Hrd⟩
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
        iframe Hg Hvt He Hw Ht
        isplitr [HA O0 O4 O16 Hrd S0 S4 S8 Hw']
        · ihave C := stk_intro n _ _ $$ C
          rw [show (bytes32 4 ++ sc8).length = 12 by simp; omega]
          ihave C := stk_addr (show (sp - 48 + 32).toNat = (sp - 48).toNat + 32 by
            rw [UInt32.toNat_add, h48]; simp; omega) $$ C
          ihave J1 := stk_join n ((sp - 48).toNat + 32) 12 4 $$ [C S4']
          · rw [show (sp - 48).toNat + 32 + 12 = (sp - 48).toNat + 32 + 4 + 8 by omega]; iframe C S4'
          ihave J2 := stk_join n (sp - 48).toNat 32 16 $$ [SF J1]
          · iframe SF J1
          ihave S80 := stk_addr (show (sp - 48).toNat - 80 = sp.toNat - 192 + 64 by omega) $$ S80
          ihave J3 := stk_join n (sp.toNat - 192) 64 80 $$ [S64 S80]
          · iframe S64 S80
          ihave J2 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ J2
          iapply stk_join n (sp.toNat - 192) 144 48
          iframe J3 J2
        iunfold resStr
        rw [hres]
        iunfold errStr
        iexists q, p, cap, bs.length, hl', F', acc
        isplitr
        · ipureintro; exact ⟨hq, le_rfl, hhl⟩
        rw [show (ob.drop 8) = ob.drop 8 from rfl]
        iframe O0 O4 O16 Hrd S0 S4 S8
        iapply ParseEscape.sbufE_intro
        iframe HA Hw'
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      have e1 : (30 * body.length + 450) * cfg.regularOpCost = 30 * body.length * cfg.regularOpCost + 450 * cfg.regularOpCost :=
        Nat.add_mul _ _ _
      have e2 : 30 * (j + body.length - j) * cfg.regularOpCost = 30 * body.length * cfg.regularOpCost := by
        rw [show j + body.length - j = body.length by omega]
      ipureintro; omega
    inext
    iintro Hc
    iapply invS_intro n inst mi Cg cfg.regularOpCost 450 (Z + Rl) out de sc (sp - 48) _ _ _ ptr j body.length _ j _
      le_rfl (by omega)
    iframe Hc D8 Hs Ho He Hw Ht Hvt D0 D4 Hb Hg S0 S4 S8 Hsb
  · isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    inext
    iintro Hc
    iexists i, [], ptrS, capS, hl, F, 0, 0, 0, 0, 0, 0
    iframe Hc Hs Ho He Hw Ht Hvt Hg D0 D4 D8 Hb S0 S4 Hsb
    isplitr
    · ipureintro
      refine ⟨rfl, rfl, le_rfl, hi, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun h => absurd rfl h, by simp, by simp, le_rfl, hroom⟩
    iexact S8

end L646e

end WNear.Binary.ParseStr
