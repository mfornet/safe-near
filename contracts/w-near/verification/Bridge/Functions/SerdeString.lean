import Bridge.Functions.SerdeErrBox
import Bridge.Functions.FmtSink

/-!
# serde's `String` from a `&str` (M6): `visit_str` (633), `to_owned` (618) and `RawVec<u8>`'s
allocation (626, 624, 625 at alignment 1; the layout 607/608)

`deserialize_str` (380) hands the decoded string to `StringVisitor::visit_str` (633), which copies it
into a fresh `String`:

```wat
;; 633 visit_str(out, p, n)          618(sp, p, n); out := Ok(String) = (0, ptr, cap, len)
;; 618 to_owned(out, p, n)           (ptr, cap) := allocate_in(n, uninit) (626); memcpy(ptr, p, n)
;;                                   (951); out := (ptr, cap, n)
;; 626 allocate_in(out, n, 0)        (size, align) := Layout::array::<u8>(n) (608) = (n, 1);
;;                                   size < 2^31; (ptr, size) := Global::allocate(size, 1) (624)
;;                                   ptr = 0 → handle_alloc_error (842, not reached)
;; 608 Layout::array(out, n)         607 on (n, 1): out := ((n + 1 - 1) & -1, 1)
;; 624 Global::allocate(out, s, 1)   625(sp, s, 1, false) in a 16-byte frame
;; 625 alloc_impl(out, s, 1, false)  s = 0 → (1, 0) (dangling); else __rust_alloc(s, 1) (310)
```

`heapS` is the heap after `RawVec<u8>`'s allocation of `size` bytes at `p`: unchanged with `p = 1`
for `size = 0`, else the block `(p, size)` lent (`p ≠ 0`, below `2^32`), the memory maybe grown by
`grownLen`, the free list bound `max F 1`. Costs are upper bounds through `costS cfg F size`, the
allocator's `cost310W cfg F size 1` and a constant.

* `f625_s`, `f624_s`, `f607_s`, `f608_s`, `f626_s`: the allocation;
* `f618_s`: `to_owned`, the bytes `bs` copied into the fresh block;
* `f633_s`: `visit_str`, `Ok(String)` holding `bs`.
-/

namespace WNear.Binary.SerdeString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr stk_open581 stk_close581
  roomFor grownLen)

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The heap after `RawVec<u8>`'s allocation of `size` bytes at `p`. -/
def heapS (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (size p : UInt32) : IProp GF :=
  if size = 0 then iprop(⌜p = 1⌝ ∗ heapInv n maxP len live F)
  else iprop(⌜p ≠ 0 ∧ p.toNat + size.toNat < 2 ^ 32⌝ ∗ ∃ len', ⌜len' = len ∨ len' = grownLen len size⌝ ∗
    heapInv n maxP len' ((p.toNat, size.toNat) :: live) (max F 1))

end Defs

/-- The allocator's part of the cost. -/
abbrev costA (cfg : WasmConfig) (F : Nat) (size : UInt32) : Nat := AllocWalk.cost310W cfg F size 1

theorem heapS_bound {GF : BundledGFunctors} [WasmGS NearState GF] (n maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (size p : UInt32) :
    heapS (GF := GF) n maxP len live F size p ⊢ ⌜p.toNat + size.toNat < 2 ^ 32⌝ ∗ heapS n maxP len live F size p := by
  by_cases h0 : size = 0
  · simp only [heapS, if_pos h0]
    iintro ⟨%hp, H⟩
    isplitr
    · ipureintro; subst hp h0; decide
    iframe H
    ipureintro; exact hp
  · simp only [heapS, if_neg h0]
    iintro ⟨%⟨hp, hb⟩, H⟩
    isplitr
    · ipureintro; exact hb
    iframe H
    ipureintro; exact ⟨hp, hb⟩

section L625

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Global::alloc_impl(out, size, 1, false)`** (625), any `size` (`< 2^28`) with room: `(p, size)`
at `out`, `heapS`. -/
theorem f625_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ob : List UInt8) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) (hsp : 16 ≤ sp.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f625 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 size, .i32 1, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 30 * cfg.regularOpCost + costA cfg F size)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ vt n 1057464 idx ta (A 578) ∗ heapS n maxP len live F size p ∗
          block n p.toNat size.toNat ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size)) := by
  iintro ⟨#Hcode, #H310⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha310 := hm.funcs 310 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  simp only [f625, costA]
  generalize hK : AllocWalk.cost310W cfg F size 1 = K
  rw [show 30 * cfg.regularOpCost + K + R = 30 * cfg.regularOpCost + (K + R) by omega]
  by_cases hs0 : size = 0
  · subst hs0
    repeat mstep
    mstep [Ho4]; mstep; mstep; mstep [Ho0]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    isplitr
    · ipureintro; trivial
    iexists 1
    iframe Hg Hs Hvt Ho0 Ho4
    iunfold heapS
    rw [if_pos rfl]
    iframe Hinv
    isplitr
    · ipureintro; rfl
    iunfold block
    iexists []
    isplitr
    · ipureintro; rfl
    iapply VecFromElem.memBytes_nil
  · have hsize : 1 ≤ size.toNat := by
      rcases Nat.eq_zero_or_pos size.toNat with h | h
      · exact absurd (UInt32.toNat_inj.mp (by simpa using h)) hs0
      · exact h
    obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr (by omega)
    icases stk_open581 n sp hsp $$ Hs with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mstep; mstep
    have key := AllocWalk.f310_spec_walk (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega)
      Cg gt sp size 1 idx 0 maxP len live F o1 o2 o4 hsp (by simp) (by simp) hsize hsize2 hlen0 hlen1 h1 h2 h4 hroom hmax
    rw [hK] at key
    clear hK
    mstep; mstep
    mcall key using [Hg O1 O2 O4 Hvt Hinv]
    · iframe Hg O1 O2 O4 Hvt Hinv
    icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
    subst hrs
    clear key hroom hmax hlen0 hlen1 h1 h2 h4
    ihave Hinv := FmtSink.heapInv_bound (p := p.toNat) (s := size.toNat) (by simp) $$ Hinv
    icases Hinv with ⟨%hpb, Hinv⟩
    ihave HA : heapS n maxP len live F size p $$ [Hinv]
    · iunfold heapS
      rw [if_neg hs0]
      isplitr
      · ipureintro; exact ⟨hp0, hpb⟩
      iexists len'
      iframe Hinv
      ipureintro; exact hl'
    clear hl'
    have hpc : p ≠ 0 := hp0
    mcredits (11 * cfg.regularOpCost + R)
    mstep; mstep
    iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr
    · ipureintro; exact ⟨rfl, hpc⟩
    mctrl_norm; repeat mpay
    mstep; mstep; mstep [Ho4]
    mstep; mstep; mstep [Ho0]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    isplitr
    · ipureintro; trivial
    iexists p
    iframe Hg Hvt Ho0 Ho4 HA Hb
    iapply stk_close581 n sp hsp
    iframe HO W8

end L625


section L607

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (pre684 post684 pre685 post685 layout_size ofNat_decode_pair storeBytes_pair64
  stk16 stk16_join)
open WNear.Binary.AllocNewCell (memBytes_addr)


/-- `Layout::array::<u8>` (607) on `(c, 1)`: the layout `(c, 1)` at `out`. -/
theorem f607_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (Cg : Nat)
    (gt : GlobalType) (s out lp c : UInt32) (ob0 ob4 : List UInt8)
    (hob0 : ob0.length = 4) (hob4 : ob4.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f607 Cg (pre684 n g gt s out lp c ob0 ob4)
        (fun _ => 33 * cfg.regularOpCost) (post684 n g gt s out lp c) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre684 at HP
  icases HP with ⟨%hargs, Hg, Hc0, Hc4, Ho0, Ho4⟩
  subst hargs
  simp only [f607]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [Hc4]; mstep; mstep; mstep; mstep; mstep
  mstep; mstep [Hc0]; mstep
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  simp only [UInt32.reduceOfNat]
  rw [layout_size]
  mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post684
  iframe Hg Hc0 Hc4 Ho0 Ho4
  ipureintro; simp [htype]


/-- `Layout::array::<u8>(cap)` (608): `(cap, 1)` at `out`. -/
theorem f608_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (ob : List UInt8) (hob : ob.length = 8)
    (hs : 16 ≤ s.toNat) :
    A 607 ↪[wf] FuncInst.wasm types[14]! inst f607 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f608 Cg (pre685 n g gt s out c ob)
        (fun _ => 67 * cfg.regularOpCost) (post685 n g gt s out c) := by
  iintro ⟨#H684, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha684 := hm.funcs 607 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 16 + 8 := by simp [UInt32.toNat_add, h16]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre685 at HP
  icases HP with ⟨%hargs, Hg, Hs, Ho⟩
  subst hargs
  icases stk16 n (s.toNat - 16) $$ Hs with ⟨W0, W4, W8, W12⟩
  iunfold stk at W0 W4 W8 W12
  icases W0 with ⟨%b0, %hb0, W0⟩
  icases W4 with ⟨%b4, %hb4, W4⟩
  icases W8 with ⟨%b8, %hb8, W8⟩
  icases W12 with ⟨%b12, %hb12, W12⟩
  simp only [f608]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [W12]
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep; mstep
  mcall (f607_s cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg Cg gt (s - 16) (s - 16)
      (s - 16 + 8) c b0 b4 hb0 hb4) using [Hg W0 W4 W8 W12]
  · iunfold pre684
    ihave W8 := memBytes_addr (show s.toNat - 16 + 8 = (s - 16 + 8).toNat by omega) $$ W8
    ihave W12 := memBytes_addr (show s.toNat - 16 + 12 = (s - 16 + 8).toNat + 4 by omega) $$ W12
    ihave W0 := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ W0
    ihave W4 := memBytes_addr (show s.toNat - 16 + 4 = (s - 16).toNat + 4 by omega) $$ W4
    iframe Hg W0 W4 W8 W12
    ipureintro; rfl
  iunfold post684 at HQ
  icases HQ with ⟨%hrs, Hg, W8, W12, W0, W4⟩
  subst hrs
  ihave W0 := KeyGet.join64 n (s - 16).toNat c 1 $$ [W0 W4]
  · iframe W0 W4
  mstep; mstep; mstep [W0]
  rw [ofNat_decode_pair]
  mstep [Ho]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  ihave W0 := KeyGet.split64 n (s - 16).toNat c 1 $$ W0
  icases W0 with ⟨W0, W4⟩
  ihave Ho := KeyGet.split64 n out.toNat c 1 $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  iunfold post685
  iframe Hg Ho0 Ho4
  isplitr
  · ipureintro; simp [htype]
  iapply stk16_join
  ihave W0 := stk_word n _ c $$ W0
  ihave W4 := stk_word n _ 1 $$ W4
  ihave W8 := stk_word n _ c $$ W8
  ihave W12 := stk_word n _ 1 $$ W12
  rw [h16, e8]
  iframe W0 W4 W8 W12

end L607

end WNear.Binary.SerdeString

namespace WNear.Binary.SerdeString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor grownLen)

theorem heapS_ne {GF : BundledGFunctors} [WasmGS NearState GF] {n maxP len : Nat}
    {live : List (Nat × Nat)} {F : Nat} {size p : UInt32} :
    heapS (GF := GF) n maxP len live F size p ⊢ ⌜p ≠ 0⌝ ∗ heapS n maxP len live F size p := by
  by_cases h0 : size = 0
  · simp only [heapS, if_pos h0]
    iintro ⟨%hp, H⟩
    isplitr
    · ipureintro; subst hp; decide
    iframe H
    ipureintro; exact hp
  · simp only [heapS, if_neg h0]
    iintro ⟨%⟨hp, hb⟩, H⟩
    isplitr
    · ipureintro; exact hp
    iframe H
    ipureintro; exact ⟨hp, hb⟩

section L624

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Global::allocate(out, size, 1)`** (624): 625 in a 16-byte frame, its `(p, size)` copied to
`out`. -/
theorem f624_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ob : List UInt8) (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) (hsp : 32 ≤ sp.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
      A 625 ↪[wf] FuncInst.wasm types[45]! inst f625
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f624 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 70 * cfg.regularOpCost + costA cfg F size)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 32) 32 ∗ vt n 1057464 idx ta (A 578) ∗ heapS n maxP len live F size p ∗
          block n p.toNat size.toNat ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size)) := by
  iintro ⟨#Hcode, #H310, #H625⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha625 := hm.funcs 625 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  icases stk_split n (sp.toNat - 32) 16 16 $$ Hs with ⟨S16, Hs⟩
  icases stk_split n (sp.toNat - 32 + 16) 8 8 $$ Hs with ⟨S8, S8'⟩
  iunfold stk at S8'
  icases S8' with ⟨%s8, %hs8, S8'⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  simp only [f624]
  have key := f625_s (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (sp - 16)
    (sp - 16 + 8) size idx maxP len live F s8 hs8 (by omega) (by omega) hsize2 hr
  generalize hK : costA cfg F size = K at key ⊢
  rw [show 70 * cfg.regularOpCost + K + R = 70 * cfg.regularOpCost + (K + R) by omega]
  ihave S16 := stk_addr (show sp.toNat - 32 = (sp - 16).toNat - 16 by omega) $$ S16
  ihave S8' := AllocNewCell.memBytes_addr (show sp.toNat - 32 + 16 + 8 = (sp - 16 + 8).toNat by omega) $$ S8'
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall key using [Hg S16 Hvt Hinv S8']
  · iframe Hg S16 Hvt Hinv S8'
  icases HQ with ⟨%hrs, %p, Hg, S16, Hvt, HA, Hb, P0, P4⟩
  subst hrs
  clear key
  mcredits (18 * cfg.regularOpCost + R)
  mstep; mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep [Ho0]
  mstep; mstep; mstep [P4] with (simp [UInt32.toNat_add]; omega)
  mstep [Ho4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists p
  iframe Hg Hvt HA Hb Ho0 Ho4
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P8 := stk_join n (sp - 16 + 8).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P8 := stk_addr (show (sp - 16 + 8).toNat = sp.toNat - 32 + 16 + 8 by omega) $$ P8
  ihave S16' := stk_join n (sp.toNat - 32 + 16) 8 8 $$ [S8 P8]
  · iframe S8 P8
  ihave S16 := stk_addr (show (sp - 16).toNat - 16 = sp.toNat - 32 by omega) $$ S16
  iapply stk_join n (sp.toNat - 32) 16 16
  iframe S16 S16'

end L624

section L626

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (pre685 post685 les_neg1 stk64 stk64_join)
open WNear.Binary.AllocNewCell (memBytes_addr)

/-- The code of the allocation and the copy (persistent). -/
def strCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
    A 625 ↪[wf] FuncInst.wasm types[45]! inst f625 ∗ A 624 ↪[wf] FuncInst.wasm types[31]! inst f624 ∗
    A 607 ↪[wf] FuncInst.wasm types[14]! inst f607 ∗ A 608 ↪[wf] FuncInst.wasm types[14]! inst f608 ∗
    A 626 ↪[wf] FuncInst.wasm types[31]! inst f626 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    A 618 ↪[wf] FuncInst.wasm types[31]! inst f618)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (strCode (GF := GF) n maxP inst mi A) := by
  unfold strCode; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`RawVec::<u8>::allocate_in(out, c, uninit)`** (626): the layout `(c, 1)` (608), then 624:
`(ptr, c)` at `out`, `heapS`; `c < 2^28`, with room when `c > 0`. -/
theorem f626_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (hob : ob.length = 8) (hs : 64 ≤ s.toNat)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f626 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 c, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 240 * cfg.regularOpCost + costA cfg F c)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 64) 64 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗
          heapS n maxP len live F c p ∗ block n p.toNat c.toNat)) := by
  iintro #Hv
  iunfold strCode at Hv
  icases Hv with ⟨#Hcode, #H310, #H625, #H624, #H607, #H608, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha608 := hm.funcs 608 (by decide)
  have ha624 := hm.funcs 624 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hle := les_neg1 c (by omega)
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Ho0, Ho4⟩
  icases stk64 n (s.toNat - 64) $$ Hs with ⟨R1, R2, U, Z8, Z16, L⟩
  iunfold stk at L
  icases L with ⟨%lb, %hlb, L⟩
  simp only [f626]
  generalize hK : costA cfg F c = K
  rw [show 240 * cfg.regularOpCost + K + R = 240 * cfg.regularOpCost + (K + R) by omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (f608_s cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 24) c lb hlb (by omega)) using [Hg R2 L]
  · iunfold pre685
    ihave R2 := stk_addr (show s.toNat - 64 + 16 = (s - 32).toNat - 16 by omega) $$ R2
    ihave L := memBytes_addr (show s.toNat - 64 + 56 = (s - 32 + 24).toNat by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ L
    iframe Hg R2 L
    ipureintro; rfl
  iunfold post685 at HQ
  icases HQ with ⟨%hrs, Hg, R2, L0, L4⟩
  subst hrs
  ihave R2 := stk_addr (show (s - 32).toNat - 16 = s.toNat - 64 + 16 by omega) $$ R2
  mstep; mstep; mstep; mstep [L4] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep
  mstep; mstep [L0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep
  mstep; mstep
  iunfold stk at Z16
  icases Z16 with ⟨%zb, %hzb, Z⟩
  mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  have key := f624_s (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 16) c idx maxP len live F zb hzb (by rw [UInt32.toNat_add, h32]; simp; omega) (by omega) hc28 hr
  rw [hK] at key
  mcall key using [Hg R1 R2 Hvt Hinv Z]
  · ihave R1 := stk_join n (s.toNat - 64) 16 16 $$ [R1 R2]
    · iframe R1 R2
    ihave R1 := stk_addr (show s.toNat - 64 = (s - 32).toNat - 32 by omega) $$ R1
    ihave Z := memBytes_addr (show s.toNat - 64 + 48 = (s - 32 + 16).toNat by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ Z
    iframe Hg R1 Hvt Hinv Z
    ipureintro; rfl
  clear key
  icases HQ with ⟨%hrs, %p, Hg, R1, Hvt, HA, Hb, Z0, Z4⟩
  subst hrs
  ihave HA := heapS_ne $$ HA
  icases HA with ⟨%hp0, HA⟩
  mcredits (23 * cfg.regularOpCost + R)
  mstep; mstep [Z4] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [Z0] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep; mstep
  mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Ho0 Ho4 HA Hb
  ihave R1 := stk_addr (show (s - 32).toNat - 32 = s.toNat - 64 by omega) $$ R1
  ihave R1 := stk_split n (s.toNat - 64) 16 16 $$ R1
  icases R1 with ⟨R1, R2⟩
  ihave Z0 := stk_word n _ p $$ Z0
  ihave Z4 := stk_word n _ c $$ Z4
  ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
  · iframe Z0 Z4
  ihave Z := stk_addr (show (s - 32 + 16).toNat = s.toNat - 64 + 48 by rw [UInt32.toNat_add, h32]; simp; omega) $$ Z
  ihave L0 := stk_word n _ c $$ L0
  ihave L4 := stk_word n _ 1 $$ L4
  ihave L := stk_join n _ 4 4 $$ [L0 L4]
  · iframe L0 L4
  ihave L := stk_addr (show (s - 32 + 24).toNat = s.toNat - 64 + 56 by rw [UInt32.toNat_add, h32]; simp; omega) $$ L
  iapply stk64_join
  iframe R1 R2 U Z8 Z
  iexact L

end L626

end WNear.Binary.SerdeString

namespace WNear.Binary.SerdeString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor grownLen
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)

/-- `to_owned`'s cost: the allocation's, the copy's and a constant. -/
def cost618 (cfg : WasmConfig) (F : Nat) (c : UInt32) : Nat :=
  (100 + MemCpy.cost c.toNat) * cfg.regularOpCost + (240 * cfg.regularOpCost + costA cfg F c)

section L618

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<[u8]>::to_owned(out, src, c)`** (618): a fresh block (626) holding the `c` bytes `bs` at `src`
(951): the `Vec` `(p, c, c)` at `out`. -/
theorem f618_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob bs : List UInt8) (hob : ob.length = 12) (hs : 80 ≤ s.toNat)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = c.toNat) (hsrc : src.toNat + c.toNat ≤ 2 ^ 32)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f618 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 src, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ src.toNat ] bs))
        (fun _ => cost618 cfg F c)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗
          n ↦[i32][ out.toNat + 8 ] c ∗ heapS n maxP len live F c p ∗ n ↦[wms][ p.toNat ] bs ∗
          n ↦[wms][ src.toNat ] bs)) := by
  iintro #Hv
  ihave #Hv' := Hv
  iunfold strCode at Hv'
  icases Hv' with ⟨#Hcode, #H310, #H625, #H624, #H607, #H608, #H626, #H951, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha626 := hm.funcs 626 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have t15r : types[15]!.results.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (s - 16 + 8).toNat = s.toNat - 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hsrc⟩
  subst hargs
  icases stk_split n (s.toNat - 80) 64 16 $$ Hs with ⟨S64, Hs⟩
  icases stk_split n (s.toNat - 80 + 64) 8 8 $$ Hs with ⟨S8, Z⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
  simp only [f618, cost618]
  generalize hK : costA cfg F c = K
  generalize hM : MemCpy.cost c.toNat * cfg.regularOpCost = M
  rw [show (100 + MemCpy.cost c.toNat) * cfg.regularOpCost + (240 * cfg.regularOpCost + K) + R =
    100 * cfg.regularOpCost + ((240 * cfg.regularOpCost + K) + (M + R)) by rw [Nat.add_mul, hM]; omega]
  have key := f626_s (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16 + 8) c idx maxP len live F zb hzb (by omega) (by omega) hc28 hr
  rw [hK] at key
  ihave S64 := stk_addr (show s.toNat - 80 = (s - 16).toNat - 64 by omega) $$ S64
  ihave Z := memBytes_addr (show s.toNat - 80 + 64 + 8 = (s - 16 + 8).toNat by omega) $$ Z
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mcall key using [Hg S64 Hvt Hinv Z]
  · iframe Hg S64 Hvt Hinv Z
  clear key
  icases HQ with ⟨%hrs, %p, Hg, S64, Hvt, P0, P4, HA, Hb⟩
  subst hrs
  mcredits (70 * cfg.regularOpCost + (M + R))
  ihave HA := heapS_bound $$ HA
  icases HA with ⟨%hpb, HA⟩
  iunfold block at Hb
  icases Hb with ⟨%bb, %hbb, Hb⟩
  mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep; mstep [P4] with (simp [UInt32.toNat_add]; omega)
  mstep [O4]
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep
  have hM2 : (11 + MemCpy.cost c.toNat) * cfg.regularOpCost = 11 * cfg.regularOpCost + M := by
    rw [Nat.add_mul, hM]
  mcall (MemCpy.f951_spec cfg lim (d + 1) types[15]! t15r inst mi n hn Cg p src c bb bs
      (by omega) hbs (by omega) hsrc) using [Hb Hsrc]
  · iunfold MemCpy.pre
    iframe Hb Hsrc
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hb, Hsrc⟩
  subst hrs
  try rw [hM2]
  mcredits (40 * cfg.regularOpCost + R)
  mstep
  mstep; mstep; mstep [O8]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists p
  iframe Hg Hvt O0 O4 O8 HA Hb Hsrc
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave P8 := stk_join n (s - 16 + 8).toNat 4 4 $$ [P0 P4]
  · iframe P0 P4
  ihave P8 := stk_addr (show (s - 16 + 8).toNat = s.toNat - 80 + 64 + 8 by omega) $$ P8
  ihave S16 := stk_join n (s.toNat - 80 + 64) 8 8 $$ [S8 P8]
  · iframe S8 P8
  ihave S64 := stk_addr (show (s - 16).toNat - 64 = s.toNat - 80 by omega) $$ S64
  iapply stk_join n (s.toNat - 80) 64 16
  iframe S64 S16

end L618

end WNear.Binary.SerdeString

namespace WNear.Binary.SerdeString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor grownLen
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)

section L633

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`StringVisitor::visit_str(out, src, c)`** (633): `Ok(String)`, `(0, p, c, c)` at `out`, the
`String` a fresh block holding the `c` bytes `bs` at `src` (618). -/
theorem f633_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob bs : List UInt8) (hob : ob.length = 16) (hs : 96 ≤ s.toNat)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hbs : bs.length = c.toNat) (hsrc : src.toNat + c.toNat ≤ 2 ^ 32)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f633 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 src, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ src.toNat ] bs))
        (fun _ => 60 * cfg.regularOpCost + cost618 cfg F c)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
          n ↦[i32][ out.toNat + 8 ] c ∗ n ↦[i32][ out.toNat + 12 ] c ∗ heapS n maxP len live F c p ∗
          n ↦[wms][ p.toNat ] bs ∗ n ↦[wms][ src.toNat ] bs)) := by
  iintro #Hv
  ihave #Hv' := Hv
  iunfold strCode at Hv'
  icases Hv' with ⟨#Hcode, -, -, -, -, -, -, -, #H618⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha618 := hm.funcs 618 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hsrc⟩
  subst hargs
  icases stk_split n (s.toNat - 96) 80 16 $$ Hs with ⟨S80, Hs⟩
  icases stk_split n (s.toNat - 96 + 80) 12 4 $$ Hs with ⟨Z, S4⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
  simp only [f633]
  generalize hK : cost618 cfg F c = K
  have key := f618_s (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16) src c idx maxP len live F zb bs hzb (by omega) (by omega) hbs hsrc hc28 hr
  rw [hK] at key
  ihave S80 := stk_addr (show s.toNat - 96 = (s - 16).toNat - 80 by omega) $$ S80
  ihave Z := memBytes_addr (show s.toNat - 96 + 80 = (s - 16).toNat by omega) $$ Z
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hg S80 Hvt Hinv Z Hsrc]
  · iframe Hg S80 Hvt Hinv Z Hsrc
  clear key
  icases HQ with ⟨%hrs, %p, Hg, S80, Hvt, P0, P4, P8, HA, Hb, Hsrc⟩
  subst hrs
  mcredits (35 * cfg.regularOpCost + R)
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [P8] with (simp [UInt32.toNat_add]; omega)
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  ihave P04 := KeyGet.join64 n (s - 16).toNat p c $$ [P0 P4]
  · iframe P0 P4
  mstep; mstep; mstep [P04]
  rw [ofNat_decode_pair]
  mstep [O4]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iexists p
  ihave O4 := KeyGet.split64 n (out.toNat + 4) p c $$ O4
  icases O4 with ⟨O4, O8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega, show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  iframe Hg Hvt O0 O4 O8 O12 HA Hb Hsrc
  ihave P04 := stk_intro n _ _ $$ P04
  ihave P8 := stk_word n _ _ $$ P8
  rw [show (bytes32 p ++ bytes32 c).length = 8 by simp]
  ihave Z := stk_join n (s - 16).toNat 8 4 $$ [P04 P8]
  · iframe P04 P8
  ihave Z := stk_addr (show (s - 16).toNat = s.toNat - 96 + 80 by omega) $$ Z
  ihave Z := stk_join n (s.toNat - 96 + 80) 12 4 $$ [Z S4]
  · iframe Z S4
  ihave S80 := stk_addr (show (s - 16).toNat - 80 = s.toNat - 96 by omega) $$ S80
  iapply stk_join n (s.toNat - 96) 80 16
  iframe S80 Z

end L633

end WNear.Binary.SerdeString
