import Bridge.Functions.AllocFirstFit
import Bridge.Functions.AllocWrap
import Bridge.Functions.Interface

/-!
# `WeeAlloc::alloc` (581) and `__rust_alloc` (310) on an empty free list (milestone M4)

```
alloc(&ALLOC, size, align)                                     (581; 16-byte frame at sp - 16)
  size == 0 → return align
  w := ceil(size / 4) (570);  slot (sp - 4) := ALLOC
  p := alloc_first_fit(w, align, &slot, policy, vtable) (580)
  p == 0 → new_cell_for_free_list(&out, policy, w, align) (577)
           out.tag ≠ 0 → p := 0                                -- memory.grow failed
           else cell := out.cell; cell.next_free := slot; slot := cell; p := 580 again
  ALLOC := slot;  return p
```

## What is proved

* `f581_fresh`: 581 on an **empty** free list (`ALLOC = 0`, i.e. `heapInv … 0`;
  every method's first allocation, and every allocation after a walk emptied the list),
  `1 ≤ size < 2^28`, `align = 2^k` (`k < 20`), a page-aligned memory length `len > 0`
  with room for the new chunk below `2^32` (`hroom`), the shadow stack's 16 bytes:
  `pre581` ⟶ `post581` = `∃ p, rs = [p] ∗ res581 p`, the shadow stack restored and
  - `p = 0`, `ALLOC = 0`, the memory unchanged: `memory.grow` failed; or
  - the memory grown by `P = cellPages (wordsOf size) align` pages, the fresh cell `len`
    (`prev = 0`), and 580's result on it (`AllocFirstFit.post1` with the slot being `ALLOC`):
    unlinked (`p = 0`, `ALLOC = 0`: see AllocFirstFit's finding 5), taken whole
    (`p = len + 8`), or split (`p = A`, the remainder `len` listed: `ALLOC = len`).
  Cost `630 regular_op_cost`s (an upper bound; 620 is not enough) plus `memory.grow`'s
  `linear_op_base_cost + linear_op_unit_cost * P`, the calls to 570 (→ 568), 580 (twice:
  `f580_empty`, `f580_one`), 577 (→ 572, 569, 568, 573, 574) and their activations included.
* `f310_fresh`: the same for `__rust_alloc(size, align)` through `AllocWrap`
  (`f310_of_f236`, `f236_spec`): cost `15 + 15 + 630` plus the grow charge.

## What is not done here

* Packing into the heap invariant is in `AllocFresh` (`f310_spec_fresh`): `heapInv n maxP len
  live 0` gives `pre581`, and `res581` gives back `heapInv` with the fresh chunk appended to
  the cells (`wf_freshU/W/S`; the split case needed AllocInv's `c.addr + 12 ≤ c.next`).
* Nonempty free lists (`F ≥ 1`): 580's general walk (loop invariants designed in
  AllocFirstFit's header; `f580_one` covers the one-cell list without merges).
-/

namespace WNear.Binary.AllocAlloc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocLeaves WNear.Binary.AllocFirstFit WNear.Binary.AllocNewCell
open WNear.Binary.Interface (IfaceMod)
set_option maxRecDepth 20000

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 580's result with its slot's word taken out, to be stored elsewhere (581 copies
the slot to `ALLOC`). -/
theorem post1_move (n : Nat) (w al slot c nx npv : UInt32) (lst : Bool) (bs : List UInt8)
    (pv idx : UInt32) (ta a578 : Nat) (args rs : List Value) (h : UInt32) :
    post1 (GF := GF) n w al slot c nx npv lst bs pv idx ta a578 args rs ⊢
      ∃ v r : UInt32, ⌜rs = [.i32 r]⌝ ∗ n ↦[i32][ slot.toNat ] v ∗
        (n ↦[i32][ h.toNat ] v -∗ post1 n w al h c nx npv lst bs pv idx ta a578 [] rs) := by
  iintro H
  iunfold post1 at H
  icases H with ⟨%r, %hrs, Hvt, (⟨%hp, Hs, H0, H8, Hd, Hn⟩ | ⟨%hp, Hs, H0, H8, Hd, Hn⟩ |
    ⟨%hp, Hs, H0, H8, Hd, HN0, HN1, HB, Hn⟩)⟩
  · iexists _, r; iframe Hs; isplitr; · ipureintro; exact hrs
    iintro Hh; iunfold post1; iexists r; iframe Hvt
    isplitr; · ipureintro; exact hrs
    ileft; iframe Hh H0 H8 Hd Hn; ipureintro; exact hp
  · iexists _, r; iframe Hs; isplitr; · ipureintro; exact hrs
    iintro Hh; iunfold post1; iexists r; iframe Hvt
    isplitr; · ipureintro; exact hrs
    iright; ileft; iframe Hh H0 H8 Hd Hn; ipureintro; exact hp
  · iexists _, r; iframe Hs; isplitr; · ipureintro; exact hrs
    iintro Hh; iunfold post1; iexists r; iframe Hvt
    isplitr; · ipureintro; exact hrs
    iright; iright; iframe Hh H0 H8 Hd HN0 HN1 HB Hn; ipureintro; exact hp

/-- The words of a fresh allocation: `ceil(size / 4)` as 570 computes it. -/
abbrev wordsOf (size : UInt32) : UInt32 := UInt32.ofNat ((size.toNat + 3) / 4)

/-- The fresh chunk's end: `len + pages * 65536`. -/
abbrev chunkEnd (len : Nat) (size al : UInt32) : UInt32 :=
  UInt32.ofNat len + cellPages (wordsOf size) al <<< 16

/-- What `WeeAlloc::alloc` (581) leaves on an empty free list: the shadow stack
restored (its 12 bytes, any contents), and either `memory.grow` failed (`0`, nothing
else changed), or the memory grew by `cellPages` pages, the fresh chunk's cell
`len` (its `prev` word 0) went through 580 (`post1`, the slot being `ALLOC`). -/
def res581 (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 len : Nat)
    (p : UInt32) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    ((⌜p = 0⌝ ∗ n ↦[i32][ 1074896 ] 0 ∗ n ↦[wmlength] len ∗ vt n 1057464 idx ta a578) ∨
     (n ↦[wmlength] (len + (cellPages (wordsOf size) al).toNat * pageSize) ∗ n ↦[i32][ len + 4 ] 0 ∗
      ∃ rest : List UInt8, ⌜rest.length = (cellPages (wordsOf size) al).toNat * 65536 - 12⌝ ∗
        post1 n (wordsOf size) al 1074896 (UInt32.ofNat len) (chunkEnd len size al) 0 true rest
          1057464 idx ta a578 [] [.i32 p])))

/-- 581's precondition on an empty free list: the shadow-stack global `sp` and the three
words of 581's 16-byte frame it uses, `ALLOC = 0`, the memory length, the policy's vtable slot. -/
def pre581 (n g : Nat) (gt : GlobalType) (sp idx : UInt32) (ta a578 len : Nat) (o1 o2 o4 : List UInt8) :
    IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗
    n ↦[wms][ sp.toNat - 4 ] o4 ∗ n ↦[i32][ 1074896 ] 0 ∗ n ↦[wmlength] len ∗ vt n 1057464 idx ta a578)

/-- 581's postcondition, in the shape `AllocWrap.f236_spec` takes. -/
def post581 (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 len : Nat)
    (_args rs : List Value) : IProp GF :=
  iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ res581 n g gt sp size al idx ta a578 len p)

set_option maxHeartbeats 8000000 in
theorem f581_fresh (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (len : Nat) (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          pre581 n g gt sp idx ta (A 578) len o1 o2 o4))
        (fun _ => 630 * cfg.regularOpCost + cfg.linearOpBaseCost +
          cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
        (post581 n g gt sp size al idx ta (A 578) len) := by
  iintro ⟨#H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HR⟩ Hc
  subst hargs
  iunfold pre581 at HR
  icases HR with ⟨Hg, Ho1, Ho2, Ho4, Hh, Hl, Hvt⟩
  have hglob := hm.glob
  have hmem := hm.mem
  have eS : (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 := by
    have := sp.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hS : sp - 16 = UInt32.ofNat (sp.toNat - 16) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega), eS]; simp
  have eT : (UInt32.ofNat (sp.toNat - 4)).toNat = sp.toNat - 4 := by
    have := sp.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
  have hT : UInt32.ofNat (sp.toNat - 16) + 12 = UInt32.ofNat (sp.toNat - 4) := by
    apply UInt32.toNat_inj.mp; have := sp.toNat_lt
    rw [UInt32.toNat_add, eS, eT]; simp; omega
  ihave Ho1 := memBytes_addr (show sp.toNat - 16 = (UInt32.ofNat (sp.toNat - 16)).toNat by omega) $$ Ho1
  ihave Ho2 := memBytes_addr (show sp.toNat - 12 = (UInt32.ofNat (sp.toNat - 16)).toNat + 4 by omega) $$ Ho2
  ihave Ho4 := memBytes_addr (show sp.toNat - 4 = (UInt32.ofNat (sp.toNat - 16)).toNat + 12 by omega) $$ Ho4
  have hE := Hold.mk (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = (UInt32.ofNat (sp.toNat - 4)).toNat by omega)
  have hsz0 : size ≠ 0 := by intro h; subst h; simp at hsize
  have hW := Hold.mk (show (wordsOf size).toNat = (size.toNat + 3) / 4 by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega)
  have hW570 := Hold.mk (show (size + 4 + 4294967295) / 4 = wordsOf size by
    apply UInt32.toNat_inj.mp; rw [hW.get, UInt32.toNat_div, UInt32.toNat_add, UInt32.toNat_add]; simp; omega)
  have hsp' := Hold.mk hsp
  clear eS eT hsp
  have hp32 : types[32]!.params.length = 1 := by rfl
  have hp34 : types[34]!.params.length = 5 := by rfl
  have hp45 : types[45]!.params.length = 4 := by rfl
  have h570 := hm.funcs 570 (by decide)
  have h580 := hm.funcs 580 (by decide)
  have h577 := hm.funcs 577 (by decide)
  simp only [f581]
  mstep [Hg]; mstep; mstep
  rw [hS]
  mstep; mstep [Hg]
  mstep; mstep; mstep
  mstep_taken with (simp [Numeric.bool, hsz0])
  mstep
  mcall (f570_spec cfg lim (d + 1) types[32]! (by rfl) inst mi (A 568) (hm.funcs 568 (by decide))
      types[13]! (by rfl) (by rfl) (by omega) Cg size (by omega))
    with (simp [activationGas, entryLocals, f570, hp32]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  rw [hW570.get]
  mstep; mstep; mstep; mstep [Hh]; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep; mstep
  rw [hT]
  ihave Ho4 := memBytes_addr hE.get $$ Ho4
  mstep; mstep
  rw [show (UInt32.ofNat 0 : UInt32) = 0 from rfl]
  mcall (f580_empty cfg lim (d + 1) types[34]! (by rfl) inst mi n hmem Cg (wordsOf size) al
      (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464) using [Ho4]
    with (simp [activationGas, entryLocals, f580, hp34]; omega)
  · iframe Ho4
  icases HQ with ⟨%hrs, Ho4⟩
  subst hrs
  mstep
  mstep_not_taken
  mstep; mstep; mstep; mstep
  have hal20 : al.toNat < 2 ^ 20 := by
    rw [hal]; exact Nat.pow_lt_pow_right (by omega) hk
  mcall (f577_spec cfg lim (d + 1) types[45]! (by rfl) inst mi n hmem (A 572) (A 569) (A 568) (A 573) (A 574)
      (hm.funcs 572 (by decide)) (hm.funcs 569 (by decide)) (hm.funcs 568 (by decide))
      (hm.funcs 573 (by decide)) (hm.funcs 574 (by decide)) types[32]! types[32]! types[13]! types[32]! types[0]!
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by omega) Cg
      (UInt32.ofNat (sp.toNat - 16)) 1057464 (wordsOf size) al len o1 o2
      (by rw [hW.get]; omega) hal20 (by have := hsp'.get; have := sp.toNat_lt; simp only [UInt32.toNat_ofNat']; omega)
      hlen0 ho1 ho2) using [Ho1 Ho2 Hl]
    with (simp [activationGas, entryLocals, f577, hp45]; omega)
  · iframe Ho1 Ho2 Hl
  iunfold post at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  have hPb := Hold.mk (cellPages_bounds (wordsOf size) al (by rw [hW.get]; omega) hal20)
  generalize hCP : cellPages (wordsOf size) al = CP at *
  have hCP' := Hold.mk hCP
  clear hCP
  mcredits (348 * cfg.regularOpCost + R)
  have hS16 : UInt32.ofNat (sp.toNat - 16) + 16 = sp := by
    apply UInt32.toNat_inj.mp; have := sp.toNat_lt; have := hsp'.get
    rw [UInt32.toNat_add]; simp only [UInt32.toNat_ofNat']; simp; omega
  icases HQ with (⟨Ho1, Ho2, Hl, HW0, HW1, HNF, Hrest⟩ | ⟨Ho1, Ho2, Hl⟩)
  swap
  · mstep; mstep; mstep; mstep [Ho1]
    mstep_taken with (simp [Numeric.bool])
    ihave Ho4 := memBytes_addr hE.get.symm $$ Ho4
    mstep; mstep; mstep [Ho4]; mstep [Hh]
    mstep; mstep; mstep; mstep [Hg]; mstep
    rw [hS16, htype]
    mcredits R
    iframe Hc
    iunfold post581
    iexists 0
    isplitr; · ipureintro; rfl
    iunfold res581
    iframe Hg
    isplitl [Ho1 Ho2 Ho4]
    · iexists _, _, _
      ihave Ho1 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho1
      ihave Ho2 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 4 = sp.toNat - 12 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho2
      ihave Ho4 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = sp.toNat - 4 by
        have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho4
      iframe Ho1 Ho2 Ho4
      ipureintro; simp [bytes32]
    ileft
    iframe Hh Hl Hvt
    ipureintro; rfl
  -- memory.grow succeeded: the fresh cell `len` goes on the list and 580 walks it
  have hP1 := hPb.get.1
  have hP2 := hPb.get.2
  have hlenN : (UInt32.ofNat len).toNat = len := by
    simp only [UInt32.toNat_ofNat']; omega
  have hNX : (UInt32.ofNat len + CP <<< 16).toNat = len + CP.toNat * 65536 := by
    rw [UInt32.toNat_add, hlenN, shl16_toNat CP hP2]; omega
  icases Hrest with ⟨%rest, %⟨hrl, -⟩, Hrest⟩
  ihave HW0 := memBytes_addr hlenN.symm $$ HW0
  ihave HNF := memBytes_addr (show len + 8 = (UInt32.ofNat len).toNat + 8 by omega) $$ HNF
  ihave Hrest := memBytes_addr (show len + 12 = (UInt32.ofNat len).toNat + 12 by omega) $$ Hrest
  have hF := Hold.mk (And.intro hlenN hNX)
  clear hlenN hNX
  ihave Ho4 := memBytes_addr hE.get.symm $$ Ho4
  mstep; mstep; mstep; mstep [Ho1]
  mstep_not_taken
  mstep; mstep [Ho2]; mstep; mstep; mstep [Ho4]; mstep [HNF]
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep
  rw [hT]
  ihave Ho4 := memBytes_addr hE.get $$ Ho4
  mstep; mstep
  rw [show (UInt32.ofNat 0 : UInt32) = 0 from rfl]
  mcall (f580_one cfg lim (d + 1) types[34]! (by rfl) inst mi n hmem (A 572) (A 576) (A 574) (A 578) ta
      (hm.funcs 572 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 574 (by decide)) hm.table
      types[32]! types[32]! types[0]! (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
      (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464 idx (UInt32.ofNat len)
      (UInt32.ofNat len + CP <<< 16) 0 true rest k hal (by omega)
      (by rw [hW.get]; omega) (by rw [hW.get]; omega)
      (by rw [hF.get.1]; omega) (and3_of_mod4 _ (by rw [hF.get.1]; omega))
      (and3_of_mod4 _ (by rw [hF.get.2]; omega)) (by rw [hF.get.1, hF.get.2]; omega)
      (by rw [hF.get.2]; omega) (by rw [hF.get.1, hF.get.2]; omega)) using [Ho4 HW0 HNF Hrest Hvt]
    with (simp [activationGas, entryLocals, f580, hp34]; omega)
  · rw [hm.types]; mpersist
  · iunfold oneRes
    rw [nextW_true, show w0 (UInt32.ofNat len + CP <<< 16) true = UInt32.ofNat len + CP <<< 16 ||| 2 from rfl]
    iframe Ho4 HW0 HNF Hrest Hvt
  ihave HQ := post1_move n _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1074896 $$ HQ
  icases HQ with ⟨%v, %r, %hrs, Hsl, Hk⟩
  subst hrs
  mstep
  ihave Hsl := memBytes_addr hE.get.symm $$ Hsl
  mstep; mstep; mstep [Hsl]; mstep [Hh]
  ihave HP := Hk $$ Hh
  mstep; mstep; mstep; mstep [Hg]; mstep
  rw [hS16, htype]
  mcredits R
  iframe Hc
  iunfold post581
  iexists r
  isplitr; · ipureintro; rfl
  iunfold res581
  iframe Hg
  isplitl [Ho1 Ho2 Hsl]
  · iexists _, _, _
    ihave Ho1 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat = sp.toNat - 16 by
      have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho1
    ihave Ho2 := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 4 = sp.toNat - 12 by
      have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Ho2
    ihave Hsl := memBytes_addr (show (UInt32.ofNat (sp.toNat - 16)).toNat + 12 = sp.toNat - 4 by
      have := sp.toNat_lt; have := hsp'.get; simp only [UInt32.toNat_ofNat']; omega) $$ Hsl
    iframe Ho1 Ho2 Hsl
    ipureintro; simp [bytes32]
  iright
  have hc := hCP'.get
  rw [i64_zero_hi] at *
  simp only [chunkEnd]
  rw [hc]
  iframe Hl HW1
  iexists rest
  iframe HP
  ipureintro; exact hrl


/-- `__rust_alloc(size, align)` (310 → 236 → 581) on an empty free list: `f581_fresh`
through `AllocWrap`, 30 more `regular_op_cost`s. -/
theorem f310_fresh (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (len : Nat) (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            pre581 n g gt sp idx ta (A 578) len o1 o2 o4)))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (630 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)))
        (fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581 n g gt sp size al idx ta (A 578) len p)) := by
  iintro ⟨#H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
  iapply (AllocWrap.f310_of_f236 cfg lim d type htype inst mi (A 236) (hm.funcs 236 (by decide))
    types[13]! (by rfl) (by rfl) (by omega) Cg _ _ (res581 n g gt sp size al idx ta (A 578) len) size al)
  isplitr; · iexact H236
  isplitr; · iexact Hi
  imodintro
  iapply (AllocWrap.f236_spec cfg lim (d + 1) types[13]! (by rfl) inst mi (A 581) (hm.funcs 581 (by decide))
    types[15]! (by rfl) (by rfl) (by omega) Cg
    (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ pre581 n g gt sp idx ta (A 578) len o1 o2 o4))
    (fun _ => 630 * cfg.regularOpCost + cfg.linearOpBaseCost +
      cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
    (res581 n g gt sp size al idx ta (A 578) len) size al)
  isplitr; · iexact H581
  isplitr; · iexact Hi
  imodintro
  have h581 := f581_fresh (GF := GF) cfg lim (d + 1 + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    sp size al idx k len o1 o2 o4 hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom
  rw [show post581 (GF := GF) n g gt sp size al idx ta (A 578) len =
    fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581 n g gt sp size al idx ta (A 578) len p) from rfl] at h581
  iapply h581
  mpersist

end Spec

end WNear.Binary.AllocAlloc
