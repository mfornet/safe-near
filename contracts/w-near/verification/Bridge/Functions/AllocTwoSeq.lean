import Bridge.Functions.AllocTwoPack
import Bridge.Functions.AllocTwoGen
import Bridge.Functions.AllocSeq

/-!
# `__rust_alloc` on `heapInv … 2` (M4)

`f310_two_room`: `__rust_alloc(size, 1)` from `heapInv n maxP len live 2`, with room under the limit,
gives a block and `heapInv … 2`, at the cost of `AllocSeq.f310_spec_room`. The model at entry
decides the walk:

* a list of at most one cell: `AllocSeq.f310_spec_room` (`heapInv … 1`);
* `[a, b]`, `a` with `CAN_MERGE`: `AllocTwoWalk.f580_merge`, packed on the merged model
  (`AllocTwo.mergedM`) as a one-cell list;
* `[a, b]`, `a` fits: `AllocTwoWalk.f580_first`, packed by `packWO2` / `packSO2`;
* `[a, b]`, `a` too small: `AllocTwoWalk.f580_skip`, packed on `skipM` as a one-cell list.

A successful walk over two cells costs more than 300 `regular_op_cost`s; it goes through
`AllocGen.f310_succ` (no grow on that path), a failing one (at most 300) through `f310_gen`.

## What the model must exclude (`hdeg`)

`HeapModel.wf` allows `mem0 = 0`, hence a free cell at address 0, listed second after a cell `a`
with `CAN_MERGE` (`a.next_free = 1`, `a.prev = 0`: `fl_merge` holds with `d.addr = 0`). E.g. the
cells `[0, 65536)` (free), `a = [65536, 65568)` (free, first of its chunk, `next_free = 1`),
`m = [65568, 131072)` (allocated, lent), the list `[65536, 0]`: `wf live 2`. On that heap 580's
merge reads `a.prev = 0`, sets `l9 := 0` (the `br 1` past the `select`), and `Neighbors::remove`
writes `m.prev := (m.prev & 3) | (a.prev & !3) = 0`; `m` is not page-aligned, so `Geo.first` fails
for every model that keeps the lent `m`: no `heapInv` holds after the call. So no specification
`heapInv … 2 → heapInv …` of `__rust_alloc` exists, and `FtTotalSupply.ToVecAfterFree` (whose
precondition is `heapInv … 2`) is not provable as stated. `f310_two_model` takes the model with
`hdeg` (no such list); `0 < mem0` in `HeapModel.wf` (true of every real heap: `mem0` is the
initial memory length) would imply it.
-/

namespace WNear.Binary.AllocTwo

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeqModel WNear.Binary.AllocSeq
open WNear.Binary.AllocFirstFit (post1 vt w0 aN fits canSplit aligned szN oneRes nextW nextW_true nextW_false
  and3_of_mod4)
open WNear.Binary.AllocDealloc (cellRes_free memBytes_at nodup_of_sorted cellAt_iff' mem_unique)
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq cellPages cellPages_bounds shl16_toNat)
open WNear.Binary.AllocFresh (frameH MFunSpec_frame pack_fail)
open WNear.Binary.AllocAlloc (wordsOf chunkEnd)
open WNear.Binary.AllocGen (walkQ walkSpec walkSpecK res581G pre581G f310_gen f310_succ MFunSpec_cost MFunSpec_exists)
open WNear.Binary.AllocLimit (growOk_of_room)
open WNear.Binary.Interface (IfaceMod)

section Finish

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `AllocSeq.allocOutS` with the bound 2 on the free list. -/
def allocOut2 (n maxP len E : Nat) (live : List (Nat × Nat)) (size : Nat) (al p : UInt32) (P : Nat) :
    IProp GF :=
  iprop((⌜p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗ ∃ len', ⌜len' = len ∨ len' = E⌝ ∗
      heapInv n maxP len' ((p.toNat, size) :: live) 2 ∗ block n p.toNat size) ∨
    (⌜p = 0 ∧ (¬ GrowOk len (some maxP) P ∨ 8 < al.toNat)⌝ ∗ ∃ len', ⌜len' = len ∨ len' = E⌝ ∗
      heapInv n maxP len' live 2))

theorem allocOut_two {n maxP len E : Nat} {live : List (Nat × Nat)} {size : Nat} {al p : UInt32} {P : Nat} :
    allocOutS (GF := GF) n maxP len E live size al p P ⊢ allocOut2 n maxP len E live size al p P := by
  iintro H
  iunfold allocOutS at H
  iunfold allocOut2
  icases H with (⟨%h, %len', %hl, Hi, Hb⟩ | ⟨%h, %len', %hl, Hi⟩)
  · ileft; iframe %h; iexists len'; iframe %hl Hb
    iapply heapInv_mono _ _ _ _ 1 2 (by omega) $$ Hi
  · iright; iframe %h; iexists len'; iframe %hl
    iapply heapInv_mono _ _ _ _ 1 2 (by omega) $$ Hi

theorem finishS2 {n g maxP len : Nat} {live : List (Nat × Nat)} {gt : GlobalType} {sp size al idx : UInt32}
    {ta a578 k : Nat} (Fr Z : IProp GF) (W : UInt32 → UInt32 → IProp GF)
    (hal : al.toNat = 2 ^ k) (hk : k < 20) (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hl0 : 0 < len) (hlen0 : len % 65536 = 0)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hF : Fr ∗ Z ⊢ frameH n maxP len live)
    (hW : ∀ p v : UInt32, p ≠ 0 → (Fr ∗ n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗ W p v ⊢
      vt n 1057464 idx ta a578 ∗ allocOut2 n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536)
        live size.toNat al p (cellPages (wordsOf size) al).toNat))
    (p : UInt32) :
    Fr ∗ res581G n g gt sp size al idx ta a578 len maxP Z W p ⊢
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
        n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
      vt n 1057464 idx ta a578 ∗
      allocOut2 n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
        (cellPages (wordsOf size) al).toNat := by
  have hW' : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  have hal20 : al.toNat < 2 ^ 20 := by rw [hal]; exact Nat.pow_lt_pow_right (by omega) hk
  have hPb := cellPages_bounds (wordsOf size) al (by rw [hW']; omega) hal20
  have hfit := fresh_fits (wordsOf size) al (by rw [hW']; omega) hal20
  have hNX : chunkEnd len size al = UInt32.ofNat (len + (cellPages (wordsOf size) al).toNat * 65536) := by
    apply UInt32.toNat_inj.mp
    simp only [chunkEnd]
    rw [UInt32.toNat_add, shl16_toNat _ hPb.2]
    simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨HF, HR⟩
  iunfold res581G at HR
  icases HR with ⟨Hg, Hst, HR⟩
  iframe Hg Hst
  icases HR with (⟨%hp0, %v, Hh, Hl, HW⟩ | ⟨%⟨hp0, hfail⟩, Hh, Hl, Hvt, HZ⟩ | ⟨HZ, Hl, H4, %rest, %hrl, Hpost⟩)
  · iapply hW p v hp0
    iframe HF Hh Hl HW
  · iframe Hvt
    iunfold allocOut2
    iright
    isplitr
    · ipureintro; exact ⟨hp0, Or.inl hfail⟩
    iexists len
    isplitr
    · ipureintro; exact Or.inl rfl
    iapply heapInv_mono n maxP len live 0 2 (by omega)
    iapply pack_fail
    iframe Hh Hl
    iapply hF
    iframe HF HZ
  · rw [hNX, show pageSize = 65536 from rfl]
    ihave HX := pack_grownS (GF := GF) (n := n) (maxP := maxP) (live := live) hl0 (E := len + (cellPages (wordsOf size) al).toNat * 65536) (by omega) (by omega) (by omega) hlen0 (wordsOf size) al k hal (size := size.toNat) (by omega)
      (by rw [hW']; omega) (by omega) idx ta a578 p (cellPages (wordsOf size) al).toNat $$ [HF HZ Hl H4 Hpost]
    · iframe Hl H4
      isplitl [HF HZ]
      · iapply hF; iframe HF HZ
      iexists rest
      iframe Hpost
      ipureintro; omega
    icases HX with ⟨Hvt, HX⟩
    iframe Hvt
    iapply allocOut_two $$ HX

end Finish

section Cases

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `__rust_alloc` runs (persistent), 575 included (the merge). -/
def code310 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(n ↪[wmlimit] some maxP ∗
    A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
    A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
    A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
    A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
    A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
    A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
    A 575 ↪[wf] FuncInst.wasm types[0]! inst f575 ∗ inst ↪[inst] mi)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code310 (GF := GF) n maxP inst mi A) := by
  unfold code310; infer_instance

/-- `f310_two_room`'s postcondition before the room is used: `allocOut2`. -/
abbrev postT (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) : List Value → List Value → IProp GF :=
  fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    vt n 1057464 idx ta a578 ∗
    allocOut2 n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
      (cellPages (wordsOf size) al).toNat)

/-- The cost of `__rust_alloc` (as `AllocSeq.f310_spec_room`). -/
abbrev cost310 (cfg : WasmConfig) (size al : UInt32) : Nat :=
  15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (910 * cfg.regularOpCost +
    cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat))

/-- A list of at most one cell: `AllocSeq.f310_spec_seq`. -/
theorem case_le1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (H : HeapModel) (hw : H.wf live 1) (hl : H.len = len) :
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost310 cfg size al)
        (postT n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro #Hk
  iunfold code310 at Hk
  icases Hk with ⟨#Hm, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, -, #Hi⟩
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
    (Q := postS n g gt sp size al idx ta (A 578) maxP len live) ?hP ?hQ)
  case hP =>
    intro args
    iintro HX
    iunfold preX at HX
    icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
    isplitl
    · iframe %ha Hg Ho1 Ho2 Ho4 Hvt
      iapply WNear.Binary.AllocFresh.heapInv_intro H hw hl (UInt32.ofNat H.head) rfl
      rw [hl]; iframe Hh Hl Hlim Hc
    · iempintro
  case hQ =>
    intro args rs
    iintro ⟨-, %p, %hrs, Hg, Hst, Hvt, HO⟩
    iexists p
    iframe %hrs Hg Hst Hvt
    iapply allocOut_two $$ HO
  iapply (f310_spec_seq cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k maxP len live
    o1 o2 o4 hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom)
  iframe Hm H236 H581 H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi

end Cases

section Walks

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Resources the walk returns besides its result go into both of `walkQ`'s outcomes. -/
theorem walkQ_frame (n slot : Nat) (idx : UInt32) (ta a578 : Nat) (Y Z : IProp GF) (W : UInt32 → UInt32 → IProp GF)
    (args rs : List Value) :
    Y ∗ walkQ n slot idx ta a578 Z W args rs ⊢ walkQ n slot idx ta a578 iprop(Y ∗ Z) (fun r v => iprop(Y ∗ W r v)) args rs := by
  iintro ⟨HY, H⟩
  iunfold walkQ at H
  iunfold walkQ
  icases H with ⟨%r, %hrs, (⟨%h0, Hs, Hvt, HZ⟩ | ⟨%h0, %v, Hs, HW⟩)⟩
  · iexists r; iframe %hrs; ileft; iframe %h0 Hs Hvt
    isplitl [HY]; · iexact HY
    iexact HZ
  · iexists r; iframe %hrs; iright; iframe %h0; iexists v; iframe Hs
    isplitl [HY]; · iexact HY
    iexact HW

/-- `AllocSeq.walkO` when the cell fits and is aligned: the walk does not fail. -/
theorem walkO_fit (n : Nat) (w al slot : UInt32) (c : CellM) (bs : List UInt8) (idx : UInt32) (ta a578 : Nat)
    (args rs : List Value) (hc8 : c.addr + 8 < 2 ^ 32) (hfit : fits w (UInt32.ofNat c.addr) (UInt32.ofNat c.next))
    (hali : aligned al (UInt32.ofNat c.addr)) :
    iprop(emp) ∗ post1 (GF := GF) n w al slot (UInt32.ofNat c.addr) (UInt32.ofNat c.next) (UInt32.ofNat c.addr)
        c.last bs 1057464 idx ta a578 args rs ⊢
      walkQ n slot.toNat idx ta a578 iprop(⌜False⌝) (wO n w al c bs idx ta a578) args rs := by
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨-, H⟩
  iunfold post1 at H
  icases H with ⟨%r, %hrs, Hvt, (⟨%hU, Hs, H0, H8, Hd, Hn⟩ | ⟨%hW, Hs, H0, H8, Hd, Hn⟩ |
    ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, Hn⟩)⟩
  · exfalso
    rcases hU.2 with h | ⟨-, h⟩
    · exact h hfit
    · exact h hali
  · iunfold walkQ; iexists r
    isplitr; · ipureintro; exact hrs
    iright
    isplitr
    · ipureintro
      intro h
      have := congrArg UInt32.toNat hW.1
      rw [h, UInt32.toNat_add, hcN] at this; simp at this; omega
    iexists 0
    iframe Hs
    iunfold wO
    iintro Hh
    iunfold post1
    iexists r
    iframe Hvt
    isplitr; · ipureintro; rfl
    iright; ileft
    iframe Hh H0 H8 Hd Hn
    ipureintro; exact hW
  · iunfold walkQ; iexists r
    isplitr; · ipureintro; exact hrs
    iright
    isplitr
    · ipureintro
      intro h
      have := hS.2.2
      unfold canSplit at this
      rw [← hS.1, h] at this; simp at this
    iexists UInt32.ofNat c.addr
    iframe Hs
    iunfold wO
    iintro Hh
    iunfold post1
    iexists r
    iframe Hvt
    isplitr; · ipureintro; rfl
    iright; iright
    iframe Hh H0 H8 Hd HN0 HN1 HB Hn
    ipureintro; exact hS

end Walks

section One

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem walkQ_frameF (n slot : Nat) (idx : UInt32) (ta a578 : Nat) (Y : IProp GF) (W : UInt32 → UInt32 → IProp GF)
    (args rs : List Value) :
    Y ∗ walkQ n slot idx ta a578 iprop(⌜False⌝) W args rs ⊢
      walkQ n slot idx ta a578 iprop(⌜False⌝) (fun r v => iprop(Y ∗ W r v)) args rs := by
  iintro ⟨HY, H⟩
  iunfold walkQ at H
  iunfold walkQ
  icases H with ⟨%r, %hrs, (⟨%h0, Hs, Hvt, %hF⟩ | ⟨%h0, %v, Hs, HW⟩)⟩
  · exact hF.elim
  · iexists r; iframe %hrs; iright; iframe %h0; iexists v; iframe Hs
    isplitl [HY]; · iexact HY
    iexact HW

set_option maxHeartbeats 4000000 in
/-- The end of an allocation whose walk ends on one listed cell `c` of a model `Hm` (`heapInv … 1`
around `c`): the walk's leftovers `Y` give `frO` back with the frame `Fr`; a walk of cost
`Kt ≤ 600` when `c` fits (`f310_succ`), `≤ 300` when it does not (`f310_gen`). -/
theorem finish_one (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal1 : al.toNat = 1)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    {Hm : HeapModel} {s t : List CellM} {c dn : CellM} (hw : Hm.wf live 1) (hl : Hm.len = len)
    (hc : Hm.cells = s ++ c :: t) (hdn : c.last = false → dn ∈ t ∧ dn.addr = c.next ∧ dn.prev = c.addr)
    (hfl : Hm.freeList = [c.addr]) (hcf : c.allocated = false) (hnf : c.nextFree = 0) (ha0 : 0 < c.addr)
    (bs : List UInt8) (hbs : bs.length + 4 = c.size) (h : UInt32) (PW Y Fr : IProp GF)
    (hFr : Fr ∗ Y ⊢ frO n maxP live s t c dn) (Kt : Nat)
    (hK1 : fits (wordsOf size) (UInt32.ofNat c.addr) (UInt32.ofNat c.next) → Kt ≤ 600 * cfg.regularOpCost)
    (hK2 : ¬ fits (wordsOf size) (UInt32.ofNat c.addr) (UInt32.ofNat c.next) → Kt ≤ 300 * cfg.regularOpCost) :
    code310 n maxP inst mi A ∗
      MFunSpec cfg lim (d + 1 + 1 + 1) types[34]! inst mi f580 Cg
        (fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
          .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] h ∗ PW))
        (fun _ => Kt)
        (fun args rs => iprop(Y ∗ post1 n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat c.addr)
          (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last bs 1057464 idx ta (A 578) args rs))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop((⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            (pre581G n g gt sp h len o1 o2 o4 ∗ PW))) ∗ Fr))
        (fun _ => cost310 cfg size al)
        (postT n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro ⟨#Hk, #HWk⟩
  iunfold code310 at Hk
  icases Hk with ⟨#Hm, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, -, #Hi⟩
  have hal' : al.toNat = 2 ^ 0 := hal1
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  have hcb := hw.geo.bounds c ((mem_cells hc c).mpr (Or.inr (Or.inl rfl)))
  have hlt := hw.len_lt
  by_cases hfit : fits (wordsOf size) (UInt32.ofNat c.addr) (UInt32.ofNat c.next)
  · ---------------------------------------------------------------- the walk succeeds
    iapply (MFunSpec_frame (Fr := Fr)
      (P := fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            (pre581G n g gt sp h len o1 o2 o4 ∗ PW))))
      (Q := postG n g gt sp size al idx ta (A 578) len maxP iprop(⌜False⌝)
        (fun r v => iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) r v))) ?hPF ?hQF)
    case hPF => intro args; exact .rfl
    case hQF =>
      intro args rs
      have hW2 : ∀ p v : UInt32, p ≠ 0 → (Fr ∗ n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗
          iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) p v) ⊢
          vt n 1057464 idx ta (A 578) ∗ allocOut2 n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536)
            live size.toNat al p (cellPages (wordsOf size) al).toNat) := by
        intro p v hp
        iintro ⟨HF, Hh, Hl, HY, HW⟩
        ihave Hfr := hFr $$ [HF HY]
        · iframe HF HY
        ihave HO := packOK hw hl hc hdn hfl hcf hnf ha0 size al 0 hal' hsize hsize2 bs hbs idx ta (A 578)
          (len + (cellPages (wordsOf size) al).toNat * 65536) (cellPages (wordsOf size) al).toNat p v hp
          $$ [Hfr Hh Hl HW]
        · iframe Hfr Hh Hl HW
        icases HO with ⟨Hvt, HO⟩
        iframe Hvt
        iapply allocOut_two $$ HO
      iintro ⟨HF, %p, %hrs, HR⟩
      iexists p
      isplitr; · ipureintro; exact hrs
      iapply finishS2 Fr iprop(⌜False⌝) (fun r v => iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) r v))
        hal' (by omega) hsize hsize2 hlen1 hlen0 hroom (by iintro ⟨-, %hf⟩; exact hf.elim) hW2 p
      iframe HF HR
    iapply (f310_succ cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al h idx 0 len maxP o1 o2 o4 PW
      (fun r v => iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) r v)) Kt (hK1 hfit)
      hsp hal' (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom)
    isplitr; · iexact Hm
    isplitr
    · iapply (MFunSpec_frame (Fr := iprop(emp))
        (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
          .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] h ∗ PW))
        (Q := fun args rs => iprop(Y ∗ post1 n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat c.addr)
          (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last bs 1057464 idx ta (A 578) args rs)) ?hPW ?hQW)
      case hPW => intro args; iintro H; isplitl [H]; · iexact H
                  · iempintro
      case hQW =>
        intro args rs
        iintro ⟨-, HY, HP⟩
        iapply walkQ_frameF
        iframe HY
        iapply walkO_fit n (wordsOf size) al _ c bs idx ta (A 578) args rs (by omega) hfit
          (by unfold aligned; rw [hal1]; exact Nat.mod_one _)
        isplitr; · iempintro
        iexact HP
      iexact HWk
    iframe H236 H581 H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi
  · ---------------------------------------------------------------- the walk may fail
    iapply (MFunSpec_frame (Fr := Fr)
      (P := fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            (pre581G n g gt sp h len o1 o2 o4 ∗ PW))))
      (Q := postG n g gt sp size al idx ta (A 578) len maxP iprop(Y ∗ zO n c bs)
        (fun r v => iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) r v))) ?hPG ?hQG)
    case hPG => intro args; exact .rfl
    case hQG =>
      intro args rs
      have hF2 : Fr ∗ iprop(Y ∗ zO n c bs) ⊢ frameH n maxP len live := by
        iintro ⟨HF, HY, HZ⟩
        ihave Hfr := hFr $$ [HF HY]
        · iframe HF HY
        iapply restoreO hw hl hc hdn hcf hnf bs hbs
        iframe Hfr HZ
      have hW2 : ∀ p v : UInt32, p ≠ 0 → (Fr ∗ n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗
          iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) p v) ⊢
          vt n 1057464 idx ta (A 578) ∗ allocOut2 n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536)
            live size.toNat al p (cellPages (wordsOf size) al).toNat) := by
        intro p v hp
        iintro ⟨HF, Hh, Hl, HY, HW⟩
        ihave Hfr := hFr $$ [HF HY]
        · iframe HF HY
        ihave HO := packOK hw hl hc hdn hfl hcf hnf ha0 size al 0 hal' hsize hsize2 bs hbs idx ta (A 578)
          (len + (cellPages (wordsOf size) al).toNat * 65536) (cellPages (wordsOf size) al).toNat p v hp
          $$ [Hfr Hh Hl HW]
        · iframe Hfr Hh Hl HW
        icases HO with ⟨Hvt, HO⟩
        iframe Hvt
        iapply allocOut_two $$ HO
      iintro ⟨HF, %p, %hrs, HR⟩
      iexists p
      isplitr; · ipureintro; exact hrs
      iapply finishS2 Fr iprop(Y ∗ zO n c bs)
        (fun r v => iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) r v))
        hal' (by omega) hsize hsize2 hlen1 hlen0 hroom hF2 hW2 p
      iframe HF HR
    iapply (f310_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al h idx 0 len maxP o1 o2 o4 PW
      iprop(Y ∗ zO n c bs) (fun r v => iprop(Y ∗ AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578) r v))
      hsp hal' (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom)
    isplitr; · iexact Hm
    isplitr
    · iapply (MFunSpec_frame (Fr := iprop(emp))
        (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
          .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] h ∗ PW))
        (Q := fun args rs => iprop(Y ∗ post1 n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat c.addr)
          (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last bs 1057464 idx ta (A 578) args rs)) ?hPW ?hQW)
      case hPW => intro args; iintro H; isplitl [H]; · iexact H
                  · iempintro
      case hQW =>
        intro args rs
        iintro ⟨-, HY, HP⟩
        iapply walkQ_frame
        iframe HY
        iapply walkO n (wordsOf size) al _ c bs idx ta (A 578) args rs (by omega)
        isplitr; · iempintro
        iexact HP
      iapply (MFunSpec_cost (K := fun _ => Kt) (fun _ => hK2 hfit))
      iexact HWk
    iframe H236 H581 H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi

end One

section Merge

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocTwoWalk (mergeRes mergedBs code7 code575 f580_merge)

set_option maxHeartbeats 8000000 in
/-- The list `[a, b]` with `CAN_MERGE` on `a`: `f580_merge`, then the merged model as one cell. -/
theorem case_merge (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal1 : al.toNat = 1)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (H : HeapModel) (hw : H.wf live 2) (hl : H.len = len) {s t : List CellM} {cb ca : CellM}
    (hc : H.cells = s ++ cb :: ca :: t) (hcbf : cb.allocated = false) (hcaf : ca.allocated = false)
    (hcbn : cb.next = ca.addr) (hcbnf : cb.nextFree = 0) (hhead : H.head = ca.addr) (hb0 : 0 < cb.addr)
    {t2 : List CellM} {d2 : CellM} (hw2 : (mergedM H s t cb ca).wf live 1)
    (hc2 : (mergedM H s t cb ca).cells = s ++ bM cb ca :: t2)
    (hd2 : (bM cb ca).last = false → d2 ∈ t2 ∧ d2.addr = (bM cb ca).next ∧ d2.prev = (bM cb ca).addr)
    (hopen : n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ bsa bsb : List UInt8, ⌜bsa.length + 12 + ca.addr = ca.next ∧ bsb.length + 12 + cb.addr = ca.addr⌝ ∗
      mergeRes n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last bsa bsb ∗
      frO n maxP live s t2 (bM cb ca) d2) :
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost310 cfg size al)
        (postT n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro #Hk
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have ba := hw.geo.bounds ca hca
  have bb := hw.geo.bounds cb hcb
  have hna := hw.geo.next_al ca hca
  have hlt := hw.len_lt
  have hcaN : (UInt32.ofNat ca.addr).toNat = ca.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcbN : (UInt32.ofNat cb.addr).toNat = cb.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnN : (UInt32.ofNat ca.next).toNat = ca.next := by simp only [UInt32.toNat_ofNat']; omega
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  have hal' : al.toNat = 2 ^ 0 := hal1
  -- the walk's resources out
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ y : {p : List UInt8 × List UInt8 //
        p.1.length + 12 + ca.addr = ca.next ∧ p.2.length + 12 + cb.addr = ca.addr},
      (⌜args = [.i32 size, .i32 al]⌝ ∗
        (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp (UInt32.ofNat ca.addr) len o1 o2 o4 ∗
            (mergeRes n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last y.1.1 y.1.2 ∗
              vt n 1057464 idx ta (A 578))))) ∗
      frO n maxP live s t2 (bM cb ca) d2))
    (Q := postT n g gt sp size al idx ta (A 578) maxP len live) ?hP ?hQ)
  case hP =>
    intro args
    iintro HX
    iunfold preX at HX
    icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
    icases hopen $$ [Hlim Hc] with ⟨%bsa, %bsb, %hbs, HM, Hfr⟩
    · iframe Hlim Hc
    isplitl
    · iexists ⟨(bsa, bsb), hbs⟩
      iframe Hfr
      isplitr; · ipureintro; exact ha
      isplitr; · ipureintro; rfl
      iframe HM Hvt
      iunfold pre581G
      ihave Hh := memBytes_eq (show bytes32 (UInt32.ofNat H.head) = bytes32 (UInt32.ofNat ca.addr) by
        rw [hhead]) $$ Hh
      rw [hl]
      iframe Hg Ho1 Ho2 Ho4 Hh Hl
    · iempintro
  case hQ => intro args rs; iintro ⟨-, H⟩; iexact H
  iapply MFunSpec_exists
  imodintro
  iintro %y
  obtain ⟨⟨bsa, bsb⟩, hbsa, hbsb⟩ := y
  dsimp only at hbsa hbsb ⊢
  have hbs' : (mergedBs bsb bsa (w0 (UInt32.ofNat ca.next) ca.last &&& 3) 0 (UInt32.ofNat cb.addr)).length + 4 =
      (bM cb ca).size := by
    simp [mergedBs, bytes32, bM, CellM.size]; omega
  iapply (finish_one cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live o1 o2 o4
    hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hw2 (by rw [← hl]; rfl) hc2 hd2 rfl hcbf hcbnf
    (by simp only [bM]; omega) _ hbs' (UInt32.ofNat ca.addr)
    (iprop(mergeRes n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last bsa bsb ∗
      vt n 1057464 idx ta (A 578))) iprop(emp) (frO n maxP live s t2 (bM cb ca) d2)
    (by iintro ⟨H, -⟩; iexact H)
    ((if fits (wordsOf size) (UInt32.ofNat cb.addr) (UInt32.ofNat ca.next) then 480 else 300) * cfg.regularOpCost)
    (fun h => by simp only [bM] at h; rw [if_pos h]; omega)
    (fun h => by simp only [bM] at h; rw [if_neg h]))
  iframe Hk
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
      .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] UInt32.ofNat ca.addr ∗
      mergeRes n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last bsa bsb ∗
      n ↦[i32][ (1057464 : UInt32).toNat + 16 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func (A 578)))
    (Q := post1 n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat cb.addr) (UInt32.ofNat ca.next)
      (UInt32.ofNat cb.addr) ca.last (mergedBs bsb bsa (w0 (UInt32.ofNat ca.next) ca.last &&& 3) 0 (UInt32.ofNat cb.addr))
      1057464 idx ta (A 578)) ?hPW ?hQW)
  case hPW =>
    intro args
    iintro ⟨%ha, Hs, HM, Hvt⟩
    iunfold vt at Hvt
    icases Hvt with ⟨Hv, Ht⟩
    isplitl; · iframe %ha Hs HM Hv Ht
    · iempintro
  case hQW =>
    intro args rs
    iintro ⟨-, H⟩
    isplitr; · iempintro
    simp only [bM]
    iexact H
  iunfold code310 at Hk
  icases Hk with ⟨-, -, -, -, -, -, -, #H572, -, -, #H574, #H576, #H578, #H575, #Hi⟩
  iapply (f580_merge cfg lim (d + 1 + 1 + 1) types[34]! (by rfl) inst mi n hm.mem (A 572) (A 575) (A 576) (A 574)
    (A 578) ta (hm.funcs 572 (by decide)) (hm.funcs 575 (by decide)) (hm.funcs 576 (by decide))
    (hm.funcs 574 (by decide)) hm.table types[32]! types[0]! types[32]! types[0]!
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
    (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464 idx (UInt32.ofNat ca.addr) (UInt32.ofNat cb.addr)
    (UInt32.ofNat ca.next) ca.last bsa bsb hal1 (by rw [hW]; omega) (by rw [hW]; omega)
    (and3_of_mod4 _ (by rw [hcaN]; omega)) (and3_of_mod4 _ (by rw [hcbN]; omega))
    (and3_of_mod4 _ (by rw [hnN]; exact hna)) (by rw [hcbN]; omega) (by rw [hcbN, hcaN]; omega)
    (by rw [hcaN, hnN]; omega) (by rw [hnN]; omega) (by rw [hcbN, hcaN]; omega) (by rw [hcaN, hnN]; omega)
    _ (fun h => by rw [if_pos h]) (by split <;> omega))
  iunfold code7
  iunfold code575
  rw [hm.types]
  iframe H572 H576 H574 H578 H575 Hi

end Merge

section Skip

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocTwoWalk (cellW code7 f580_skip)

set_option maxHeartbeats 8000000 in
/-- The list `[a, b]` without `CAN_MERGE`, `a` too small: `f580_skip`, then `skipM` as one cell. -/
theorem case_skip (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal1 : al.toNat = 1)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (H : HeapModel) (hw : H.wf live 2) (hl : H.len = len) {s t : List CellM} {ca cb dn : CellM}
    (hc : H.cells = s ++ cb :: t) (hdn : cb.last = false → dn ∈ t ∧ dn.addr = cb.next ∧ dn.prev = cb.addr)
    (hca : ca ∈ H.cells) (hcaf : ca.allocated = false) (hcbf : cb.allocated = false) (hab : ca ≠ cb)
    (hcanf : ca.nextFree = cb.addr) (hcbnf : cb.nextFree = 0) (hhead : H.head = ca.addr)
    (ha0 : 0 < ca.addr) (hb0 : 0 < cb.addr)
    (hfa : ¬ fits (wordsOf size) (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next)) :
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost310 cfg size al)
        (postT n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro #Hk
  have hcb : cb ∈ H.cells := (mem_cells hc cb).mpr (Or.inr (Or.inl rfl))
  have ba := hw.geo.bounds ca hca
  have bb := hw.geo.bounds cb hcb
  have hna := hw.geo.next_al ca hca
  have hnb := hw.geo.next_al cb hcb
  have hlt := hw.len_lt
  have hcaN : (UInt32.ofNat ca.addr).toNat = ca.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcbN : (UInt32.ofNat cb.addr).toNat = cb.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnaN : (UInt32.ofNat ca.next).toNat = ca.next := by simp only [UInt32.toNat_ofNat']; omega
  have hnbN : (UInt32.ofNat cb.next).toNat = cb.next := by simp only [UInt32.toNat_ofNat']; omega
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  have hcbf' : (skipM H cb.addr).cells = s ++ cb :: t := hc
  have hw1 : (skipM H cb.addr).wf live 1 :=
    wf_skip hw ((cellAt_iff' (nodup_of_sorted hw.geo.sorted)).mpr ⟨hcb, rfl⟩) hcbf hcbnf
  -- the walk's resources out
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ bs : {bs : List UInt8 // bs.length + 4 = cb.size},
      ((⌜args = [.i32 size, .i32 al]⌝ ∗
        (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp (UInt32.ofNat ca.addr) len o1 o2 o4 ∗
            (iprop(n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
              n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] UInt32.ofNat cb.addr) ∗
             cellW n (UInt32.ofNat cb.addr) (UInt32.ofNat cb.next) (UInt32.ofNat cb.addr) 0 cb.last bs.1
              1057464 idx ta (A 578))))) ∗
      (aPart n ca -∗ frO n maxP live s t cb dn))))
    (Q := postT n g gt sp size al idx ta (A 578) maxP len live) ?hP ?hQ)
  case hP =>
    intro args
    iintro HX
    iunfold preX at HX
    icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
    icases open_skip (n := n) (maxP := maxP) hw hc hdn hcbf hca hcaf hab $$ [Hlim Hc] with
      ⟨B0, B8, ⟨%bs, %hbs, Bd⟩, Bn, HA, HK⟩
    · iframe Hlim Hc
    isplitl
    · iexists ⟨bs, hbs⟩
      iframe HK
      isplitr; · ipureintro; exact ha
      isplitr; · ipureintro; rfl
      iunfold pre581G
      ihave Hh := memBytes_eq (show bytes32 (UInt32.ofNat H.head) = bytes32 (UInt32.ofNat ca.addr) by
        rw [hhead]) $$ Hh
      rw [hl]
      iframe Hg Ho1 Ho2 Ho4 Hh Hl
      iunfold aPart at HA
      icases HA with ⟨A0, A8⟩
      isplitl [A0 A8]
      · isplitl [A0]
        · iapply memBytes_at hcaN.symm (by rw [word0_free ca hcaf hna (by omega)]) $$ A0
        · iapply memBytes_at (by omega) (by rw [hcanf]) $$ A8
      iunfold cellW
      iunfold vt at Hvt
      icases Hvt with ⟨Hv, Ht⟩
      iframe Hv Ht
      isplitl [B0]
      · iapply memBytes_at hcbN.symm (by rw [word0_free cb hcbf hnb (by omega)]) $$ B0
      isplitl [B8]
      · iapply memBytes_at (by omega) (by rw [hcbnf]; rfl) $$ B8
      isplitl [Bd]
      · iapply memBytes_addr (by omega) $$ Bd
      iexact Bn
    · iempintro
  case hQ => intro args rs; iintro ⟨-, H⟩; iexact H
  iapply MFunSpec_exists
  imodintro
  iintro %y
  obtain ⟨bs, hbs⟩ := y
  dsimp only
  iapply (finish_one cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live o1 o2 o4
    hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hw1 hl hcbf' hdn rfl hcbf hcbnf hb0 bs hbs
    (UInt32.ofNat ca.addr)
    (iprop(iprop(n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] UInt32.ofNat cb.addr) ∗
      cellW n (UInt32.ofNat cb.addr) (UInt32.ofNat cb.next) (UInt32.ofNat cb.addr) 0 cb.last bs
        1057464 idx ta (A 578)))
    (iprop(n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] UInt32.ofNat cb.addr))
    (iprop(aPart n ca -∗ frO n maxP live s t cb dn)) ?hFr
    ((if fits (wordsOf size) (UInt32.ofNat cb.addr) (UInt32.ofNat cb.next) then 400 else 300) * cfg.regularOpCost)
    (fun h => by rw [if_pos h]; omega) (fun h => by rw [if_neg h]))
  case hFr =>
    iintro ⟨HK, A0, A8⟩
    iapply HK
    iunfold aPart
    isplitl [A0]
    · iapply memBytes_at hcaN (by rw [word0_free ca hcaf hna (by omega)]) $$ A0
    · iapply memBytes_at (by omega) (by rw [hcanf]) $$ A8
  iframe Hk
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
      .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] UInt32.ofNat ca.addr ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] UInt32.ofNat cb.addr ∗
      cellW n (UInt32.ofNat cb.addr) (UInt32.ofNat cb.next) (UInt32.ofNat cb.addr) 0 cb.last bs
        1057464 idx ta (A 578)))
    (Q := fun args rs => iprop(n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] UInt32.ofNat cb.addr ∗
      post1 n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat cb.addr) (UInt32.ofNat cb.next)
        (UInt32.ofNat cb.addr) cb.last bs 1057464 idx ta (A 578) args rs)) ?hPW ?hQW)
  case hPW =>
    intro args
    iintro ⟨%ha, Hs, ⟨A0, A8⟩, HB⟩
    isplitl; · iframe %ha Hs A0 A8 HB
    · iempintro
  case hQW =>
    intro args rs
    iintro ⟨-, A0, A8, H⟩
    iframe H
    iframe A0 A8
  iunfold code310 at Hk
  icases Hk with ⟨-, -, -, -, -, -, -, #H572, -, -, #H574, #H576, #H578, -, #Hi⟩
  iapply (f580_skip cfg lim (d + 1 + 1 + 1) types[34]! (by rfl) inst mi n hm.mem (A 572) (A 576) (A 574)
    (A 578) ta (hm.funcs 572 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 574 (by decide)) hm.table
    types[32]! types[32]! types[0]! (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
    (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464 idx (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next)
    (UInt32.ofNat cb.addr) (UInt32.ofNat cb.next) (UInt32.ofNat cb.addr) ca.last cb.last bs hal1
    (by rw [hW]; omega) (by rw [hW]; omega) (by rw [hcaN]; omega) (and3_of_mod4 _ (by rw [hnaN]; exact hna))
    (by rw [hcaN, hnaN]; omega) (by rw [hnaN]; omega) hfa (by rw [hcbN]; omega)
    (and3_of_mod4 _ (by rw [hcbN]; omega)) (and3_of_mod4 _ (by rw [hnbN]; exact hnb)) (by rw [hcbN, hnbN]; omega)
    (by rw [hnbN]; omega) (by rw [hcbN, hnbN]; simp only [CellM.size] at hbs; omega)
    _ (fun h => by rw [if_pos h]) (by split <;> omega))
  iunfold code7
  rw [hm.types]
  iframe H572 H576 H574 H578 Hi

end Skip

section First

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocTwoWalk (cellW code7 f580_first postF)

/-- 580's success on the first listed cell `c` (its `next_free` `b`), its slot moved to `ALLOC`. -/
def wF (n : Nat) (w al : UInt32) (c : CellM) (b : UInt32) (bs : List UInt8) (idx : UInt32) (ta a578 : Nat)
    (r v : UInt32) : IProp GF :=
  iprop(n ↦[i32][ (1074896 : UInt32).toNat ] v -∗
    postF n w al 1074896 (UInt32.ofNat c.addr) (UInt32.ofNat c.next) (UInt32.ofNat c.addr) b c.last bs
      1057464 idx ta a578 [] [.i32 r])

/-- `postF` as `walkQ`: the walk does not fail. -/
theorem walkF (n : Nat) (w al slot : UInt32) (c : CellM) (b : UInt32) (bs : List UInt8) (idx : UInt32)
    (ta a578 : Nat) (args rs : List Value) (hc8 : c.addr + 8 < 2 ^ 32) :
    iprop(emp) ∗ postF (GF := GF) n w al slot (UInt32.ofNat c.addr) (UInt32.ofNat c.next) (UInt32.ofNat c.addr) b
        c.last bs 1057464 idx ta a578 args rs ⊢
      walkQ n slot.toNat idx ta a578 iprop(⌜False⌝) (wF n w al c b bs idx ta a578) args rs := by
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨-, H⟩
  iunfold postF at H
  icases H with ⟨%r, %hrs, Hvt, (⟨%hW, Hs, H0, H8, Hd, Hn⟩ | ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, Hn⟩)⟩
  · iunfold walkQ; iexists r
    isplitr; · ipureintro; exact hrs
    iright
    isplitr
    · ipureintro
      intro h
      have := congrArg UInt32.toNat hW.1
      rw [h, UInt32.toNat_add, hcN] at this; simp at this; omega
    iexists b
    iframe Hs
    iunfold wF
    iintro Hh
    iunfold postF
    iexists r
    iframe Hvt
    isplitr; · ipureintro; rfl
    ileft
    iframe Hh H0 H8 Hd Hn
    ipureintro; exact hW
  · iunfold walkQ; iexists r
    isplitr; · ipureintro; exact hrs
    iright
    isplitr
    · ipureintro
      intro h
      have := hS.2.2
      unfold canSplit at this
      rw [← hS.1, h] at this; simp at this
    iexists UInt32.ofNat c.addr
    iframe Hs
    iunfold wF
    iintro Hh
    iunfold postF
    iexists r
    iframe Hvt
    isplitr; · ipureintro; rfl
    iright
    iframe Hh H0 H8 Hd HN0 HN1 HB Hn
    ipureintro; exact hS

set_option maxHeartbeats 8000000 in
/-- The list `[a, b]` without `CAN_MERGE`, `a` fits: `f580_first`, packed by `packWO2` / `packSO2`. -/
theorem case_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal1 : al.toNat = 1)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (H : HeapModel) (hw : H.wf live 2) (hl : H.len = len) {s t : List CellM} {ca cb dn : CellM}
    (hc : H.cells = s ++ ca :: t) (hdn : ca.last = false → dn ∈ t ∧ dn.addr = ca.next ∧ dn.prev = ca.addr)
    (hcb : cb ∈ H.cells) (hcaf : ca.allocated = false) (hcbf : cb.allocated = false) (hab : ca.addr ≠ cb.addr)
    (hcanf : ca.nextFree = cb.addr) (hcbnf : cb.nextFree = 0) (hfl : H.freeList = [ca.addr, cb.addr])
    (ha0 : 0 < ca.addr)
    (hfa : fits (wordsOf size) (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next)) :
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost310 cfg size al)
        (postT n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro #Hk
  have hca : ca ∈ H.cells := (mem_cells hc ca).mpr (Or.inr (Or.inl rfl))
  have hnd := nodup_of_sorted hw.geo.sorted
  have ba := hw.geo.bounds ca hca
  have bb := hw.geo.bounds cb hcb
  have hna := hw.geo.next_al ca hca
  have hlt := hw.len_lt
  have hcaN : (UInt32.ofNat ca.addr).toNat = ca.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcbN : (UInt32.ofNat cb.addr).toNat = cb.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnaN : (UInt32.ofNat ca.next).toNat = ca.next := by simp only [UInt32.toNat_ofNat']; omega
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  have hal' : al.toNat = 2 ^ 0 := hal1
  have hhead : H.head = ca.addr := by simp [HeapModel.head, hfl]
  have hcbat : H.cellAt cb.addr = some cb := (cellAt_iff' hnd).mpr ⟨hcb, rfl⟩
  have hnm : ∀ x ∈ t, x.addr ∈ H.freeList → x.nextFree % 2 = 0 := by
    intro x hx hxl
    rw [hfl] at hxl
    have hxH : x ∈ H.cells := (mem_cells hc x).mpr (Or.inr (Or.inr hx))
    rcases List.mem_cons.mp hxl with e | e
    · have := (pos_t hw.geo hc x hx).1; omega
    · have : x = cb := mem_unique hnd hxH hcb (by simpa using e)
      subst this; rw [hcbnf]
  have hfit' : 4 * (wordsOf size).toNat ≤ ca.next - ca.addr - 8 := by
    unfold fits szN at hfa; rw [hcaN, hnaN] at hfa; exact hfa
  -- the walk's resources out
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ bs : {bs : List UInt8 // bs.length + 4 = ca.size},
      ((⌜args = [.i32 size, .i32 al]⌝ ∗
        (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp (UInt32.ofNat ca.addr) len o1 o2 o4 ∗
            cellW n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat ca.addr) (UInt32.ofNat cb.addr)
              ca.last bs.1 1057464 idx ta (A 578)))) ∗
      frO n maxP live s t ca dn)))
    (Q := postT n g gt sp size al idx ta (A 578) maxP len live) ?hP ?hQ)
  case hP =>
    intro args
    iintro HX
    iunfold preX at HX
    icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
    icases open_one (n := n) (maxP := maxP) hw hc hdn hcaf $$ [Hlim Hc] with
      ⟨A0, A8, ⟨%bs, %hbs, Ad⟩, An, Hfr⟩
    · iframe Hlim Hc
    isplitl
    · iexists ⟨bs, hbs⟩
      iframe Hfr
      isplitr; · ipureintro; exact ha
      isplitr; · ipureintro; rfl
      iunfold pre581G
      ihave Hh := memBytes_eq (show bytes32 (UInt32.ofNat H.head) = bytes32 (UInt32.ofNat ca.addr) by
        rw [hhead]) $$ Hh
      rw [hl]
      iframe Hg Ho1 Ho2 Ho4 Hh Hl
      iunfold cellW
      iunfold vt at Hvt
      icases Hvt with ⟨Hv, Ht⟩
      iframe Hv Ht An
      isplitl [A0]
      · iapply memBytes_at hcaN.symm (by rw [word0_free ca hcaf hna (by omega)]) $$ A0
      isplitl [A8]
      · iapply memBytes_at (by omega) (by rw [hcanf]) $$ A8
      iapply memBytes_addr (by omega) $$ Ad
    · iempintro
  case hQ => intro args rs; iintro ⟨-, H⟩; iexact H
  iapply MFunSpec_exists
  imodintro
  iintro %y
  obtain ⟨bs, hbs⟩ := y
  dsimp only
  have hW2 : ∀ p v : UInt32, p ≠ 0 → (frO (GF := GF) n maxP live s t ca dn ∗ n ↦[i32][ 1074896 ] v ∗
      n ↦[wmlength] len ∗ wF n (wordsOf size) al ca (UInt32.ofNat cb.addr) bs idx ta (A 578) p v ⊢
      vt n 1057464 idx ta (A 578) ∗ allocOut2 n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536)
        live size.toNat al p (cellPages (wordsOf size) al).toNat) := by
    intro p v hp
    iintro ⟨Hfr, Hh, Hl, HW⟩
    ihave Hh := memBytes_addr (a := 1074896) (b := (1074896 : UInt32).toNat) rfl $$ Hh
    iunfold wF at HW
    ihave HP := HW $$ Hh
    iunfold postF at HP
    icases HP with ⟨%r, %hrs, Hvt, HP⟩
    obtain rfl : p = r := by simpa using hrs
    iframe Hvt
    iunfold allocOut2
    ileft
    icases HP with (⟨%hWh, Hs, H0, H8, Hd, Hn⟩ | ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, Hn⟩)
    · obtain ⟨hp', -, -⟩ := hWh
      have hpn : p.toNat = ca.addr + 8 := by
        rw [hp', UInt32.toNat_add, hcaN, show (8 : UInt32).toNat = 8 from rfl]; omega
      isplitr; · ipureintro; exact ⟨hp, by rw [hal1]; exact Nat.mod_one _⟩
      iexists len
      isplitr; · ipureintro; exact Or.inl rfl
      ihave HX := packWO2 hw hl hc hdn hcaf (wordsOf size) al p hpn hfit' (size := size.toNat) (by omega)
        (by rw [hW]; omega) bs hbs hcbat hcbf hcbnf hab.symm $$ [Hfr Hl Hs H0 H8 Hd Hn]
      · iframe Hfr Hl Hs H0 H8 Hd Hn
      icases HX with ⟨Hi, Hb⟩
      iframe Hb
      iapply heapInv_mono _ _ _ _ 1 2 (by omega) $$ Hi
    · obtain ⟨hp', -, hcs⟩ := hS
      have hcs' : ca.addr + 80 ≤ p.toNat := by unfold canSplit at hcs; rw [hcaN, ← hp'] at hcs; exact hcs
      isplitr
      · ipureintro; exact ⟨hp, by rw [hal1]; exact Nat.mod_one _⟩
      iexists len
      isplitr; · ipureintro; exact Or.inl rfl
      ihave HX := packSO2 hw hl hc hdn hcaf (wordsOf size) al p 0 hal' ha0 hp' hfit' hcs' (by rw [hW]; omega)
        (size := size.toNat) (by omega) (by rw [hW]; omega) bs hbs hfl hcanf hnm
        $$ [Hfr Hl Hs H0 H8 Hd HN0 HN1 HB Hn]
      · iframe Hfr Hl Hs H0 H8 Hd HN0 HN1 HB Hn
      iexact HX
  iapply (MFunSpec_frame (Fr := frO n maxP live s t ca dn)
    (P := fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
        (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp (UInt32.ofNat ca.addr) len o1 o2 o4 ∗
            cellW n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat ca.addr) (UInt32.ofNat cb.addr)
              ca.last bs 1057464 idx ta (A 578)))))
    (Q := postG n g gt sp size al idx ta (A 578) len maxP iprop(⌜False⌝)
      (wF n (wordsOf size) al ca (UInt32.ofNat cb.addr) bs idx ta (A 578))) ?hPF ?hQF)
  case hPF => intro args; exact .rfl
  case hQF =>
    intro args rs
    iintro ⟨HF, %p, %hrs, HR⟩
    iexists p
    isplitr; · ipureintro; exact hrs
    iapply finishS2 (frO n maxP live s t ca dn) iprop(⌜False⌝)
      (wF n (wordsOf size) al ca (UInt32.ofNat cb.addr) bs idx ta (A 578))
      hal' (by omega) hsize hsize2 hlen1 hlen0 hroom (by iintro ⟨-, %hf⟩; exact hf.elim) hW2 p
    iframe HF HR
  iunfold code310 at Hk
  icases Hk with ⟨#Hm, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, -, #Hi⟩
  iapply (f310_succ cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al (UInt32.ofNat ca.addr) idx 0 len
    maxP o1 o2 o4 _ (wF n (wordsOf size) al ca (UInt32.ofNat cb.addr) bs idx ta (A 578))
    (308 * cfg.regularOpCost) (by omega) hsp hal' (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom)
  isplitr; · iexact Hm
  isplitr
  · iapply (MFunSpec_frame (Fr := iprop(emp))
      (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
        .i32 1057464, .i32 1057464]⌝ ∗ n ↦[i32][ (UInt32.ofNat (sp.toNat - 4)).toNat ] UInt32.ofNat ca.addr ∗
        cellW n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat ca.addr) (UInt32.ofNat cb.addr)
          ca.last bs 1057464 idx ta (A 578)))
      (Q := postF n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next)
        (UInt32.ofNat ca.addr) (UInt32.ofNat cb.addr) ca.last bs 1057464 idx ta (A 578)) ?hPW ?hQW)
    case hPW => intro args; iintro H; isplitl [H]; · iexact H
                · iempintro
    case hQW =>
      intro args rs
      iintro ⟨-, H⟩
      iapply walkF n (wordsOf size) al _ ca (UInt32.ofNat cb.addr) bs idx ta (A 578) args rs (by omega)
      isplitr; · iempintro
      iexact H
    iapply (f580_first cfg lim (d + 1 + 1 + 1) types[34]! (by rfl) inst mi n hm.mem (A 572) (A 576) (A 574)
      (A 578) ta (hm.funcs 572 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 574 (by decide)) hm.table
      types[32]! types[32]! types[0]! (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
      (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464 idx (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next)
      (UInt32.ofNat ca.addr) (UInt32.ofNat cb.addr) ca.last bs hal1
      (by rw [hW]; omega) (by rw [hW]; omega) (by rw [hcaN]; omega) (and3_of_mod4 _ (by rw [hnaN]; exact hna))
      (by rw [hcaN, hnaN]; omega) (by rw [hnaN]; omega) (by rw [hcaN, hnaN]; simp only [CellM.size] at hbs; omega)
      (and3_of_mod4 _ (by rw [hcbN]; omega)) hfa _ (le_refl _))
    iunfold code7
    rw [hm.types]
    iframe H572 H576 H574 H578 Hi
  iframe H236 H581 H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi

end First

section Dispatch

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- In the sorted cells, a cell and its next neighbour are adjacent. -/
theorem adjacent {H : HeapModel} (hg : Geo H) {x y : CellM} (hx : x ∈ H.cells) (hy : y ∈ H.cells)
    (hxy : x.next = y.addr) (hxl : x.last = false) :
    ∃ s t, H.cells = s ++ x :: y :: t := by
  have hnd := nodup_of_sorted hg.sorted
  have bx := hg.bounds x hx
  obtain ⟨s0, t0, h0⟩ := List.append_of_mem hy
  have hxs : x ∈ s0 := by
    rcases (mem_cells h0 x).mp hx with h | rfl | h
    · exact h
    · omega
    · have := (pos_t hg h0 x h).1; omega
  obtain ⟨s, u, hs⟩ := List.append_of_mem hxs
  have hu : u = [] := by
    cases u with
    | nil => rfl
    | cons z u' =>
      exfalso
      have hz : z ∈ H.cells := by rw [h0, hs]; simp
      have h1 : x.addr < z.addr := by
        have hc' : H.cells = s ++ x :: (z :: u' ++ y :: t0) := by rw [h0, hs]; simp
        exact (pos_t hg hc' z (by simp)).1
      have h2 : z.addr < y.addr := by
        have hc' : H.cells = (s ++ x :: z :: u') ++ y :: t0 := by rw [h0, hs]
        exact (pos_s hg hc' z (by simp)).1
      have := hg.disj x hx z hz h1
      omega
  subst hu
  exact ⟨s, t0, by rw [h0, hs]; simp⟩

/-- The cell after a non-last cell `x` heads the cells after `x`. -/
theorem next_head {H : HeapModel} (hg : Geo H) {s t : List CellM} {x y : CellM} (hc : H.cells = s ++ x :: t)
    (hy : y ∈ H.cells) (hxy : x.next = y.addr) (hxl : x.last = false) : ∃ t', t = y :: t' := by
  have bx := hg.bounds x ((mem_cells hc x).mpr (Or.inr (Or.inl rfl)))
  have byb := hg.bounds y hy
  have hyt : y ∈ t := by
    rcases (mem_cells hc y).mp hy with h | rfl | h
    · have := (pos_s hg hc y h).2; omega
    · omega
    · exact h
  obtain ⟨t0, t1, ht⟩ := List.append_of_mem hyt
  cases t0 with
  | nil => exact ⟨t1, by simpa using ht⟩
  | cons z u =>
    exfalso
    have hz : z ∈ t := by rw [ht]; simp
    have h1 := (pos_t hg hc z hz).2
    have hc' : H.cells = (s ++ x :: z :: u) ++ y :: t1 := by rw [hc, ht]; simp
    have h2 := (pos_s hg hc' z (by simp)).1
    omega

set_option maxHeartbeats 8000000 in
/-- **`__rust_alloc(size, 1)` on a model of `heapInv … 2`**, unless its list is `[a, 0]` with
`CAN_MERGE` on `a` (`hdeg`; see the module doc): `postT` (`allocOut2`), at the cost of
`AllocSeq.f310_spec_room`. -/
theorem f310_two_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal1 : al.toNat = 1)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (H : HeapModel) (hw : H.wf live 2) (hl : H.len = len)
    (hdeg : ∀ a ca, H.freeList = [a, 0] → H.cellAt a = some ca → ca.nextFree % 2 = 0) :
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost310 cfg size al)
        (postT n g gt sp size al idx ta (A 578) maxP len live) := by
  have hal' : al.toNat = 2 ^ 0 := hal1
  have hnd := nodup_of_sorted hw.geo.sorted
  by_cases h1 : H.freeList.length ≤ 1
  · exact case_le1 cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx 0 maxP len live o1 o2 o4
      hsp hal' (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H (wf_relen hw h1) hl
  obtain ⟨a, b, hfl⟩ : ∃ a b, H.freeList = [a, b] := by
    have := hw.lists.fl_len
    match hf : H.freeList, this with
    | [], _ => rw [hf] at h1; simp at h1
    | [_], _ => rw [hf] at h1; simp at h1
    | [a, b], _ => exact ⟨a, b, rfl⟩
    | _ :: _ :: _ :: _, h => simp at h
  obtain ⟨ca, cb, hcaat, hcbat, hcaf, hcbf, hab, hcbnf, hcanf⟩ := two_facts hw hfl
  obtain ⟨hca, rfl⟩ := (cellAt_iff' hnd).mp hcaat
  obtain ⟨hcb, rfl⟩ := (cellAt_iff' hnd).mp hcbat
  have ba := hw.geo.bounds ca hca
  have bb := hw.geo.bounds cb hcb
  have hhead : H.head = ca.addr := by simp [HeapModel.head, hfl]
  -- a listed cell at address 0: the walk sees the list cut there
  by_cases ha0 : ca.addr = 0
  · have hw0 : HeapModel.wf { H with freeList := [] } live 1 :=
      ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt,
        ⟨hw.geo.bounds, hw.geo.next_al, hw.geo.sorted, hw.geo.next_nb, hw.geo.prev_nb, hw.geo.first, hw.geo.disj⟩,
        WNear.Binary.AllocFresh.lists_nil rfl, ⟨hw.lives.live_cell, hw.lives.cell_live, hw.lives.live_nodup⟩, hw.nf_lo⟩
    have e : ∀ args, preX (GF := GF) n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H args =
        preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al { H with freeList := [] } args := by
      intro args; unfold preX; rw [show HeapModel.head { H with freeList := [] } = H.head by
        simp [HeapModel.head, hfl, ha0]]
    rw [show preX (GF := GF) n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H =
      preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al { H with freeList := [] } from funext e]
    exact case_le1 cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx 0 maxP len live o1 o2 o4
      hsp hal' (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom _ hw0 hl
  by_cases hb0 : cb.addr = 0
  · have hnf0 : ca.nextFree = 0 := by
      have := hdeg ca.addr ca (by rw [hfl, hb0]) hcaat
      rcases hcanf with h | ⟨h, -⟩ <;> omega
    have hw1 : HeapModel.wf { H with freeList := [ca.addr] } live 1 :=
      ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt,
        ⟨hw.geo.bounds, hw.geo.next_al, hw.geo.sorted, hw.geo.next_nb, hw.geo.prev_nb, hw.geo.first, hw.geo.disj⟩,
        WNear.Binary.AllocFresh.lists_one (H := { H with freeList := [ca.addr] }) rfl hcaat hcaf hnf0,
        ⟨hw.lives.live_cell, hw.lives.cell_live, hw.lives.live_nodup⟩, hw.nf_lo⟩
    have e : ∀ args, preX (GF := GF) n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H args =
        preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al { H with freeList := [ca.addr] } args := by
      intro args; unfold preX; rw [show HeapModel.head { H with freeList := [ca.addr] } = H.head by
        simp [HeapModel.head, hfl]]
    rw [show preX (GF := GF) n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H =
      preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al { H with freeList := [ca.addr] } from funext e]
    exact case_le1 cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx 0 maxP len live o1 o2 o4
      hsp hal' (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom _ hw1 hl
  rcases hcanf with hcanf | ⟨hcanf, hcap⟩
  · -------------------------------------------------------------- no `CAN_MERGE`
    by_cases hfa : fits (wordsOf size) (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next)
    · obtain ⟨s, t, hc⟩ := List.append_of_mem hca
      obtain ⟨dn, hdn⟩ : ∃ dn : CellM, ca.last = false → dn ∈ t ∧ dn.addr = ca.next ∧ dn.prev = ca.addr := by
        cases hlc : ca.last
        · obtain ⟨dn, h1, h2, h3⟩ := nbr_t hw.geo hc hlc
          exact ⟨dn, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨ca, fun h => by cases h⟩
      exact case_first cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live o1 o2 o4
        hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H hw hl hc hdn hcb hcaf hcbf hab hcanf hcbnf hfl
        (by omega) hfa
    · obtain ⟨s, t, hc⟩ := List.append_of_mem hcb
      obtain ⟨dn, hdn⟩ : ∃ dn : CellM, cb.last = false → dn ∈ t ∧ dn.addr = cb.next ∧ dn.prev = cb.addr := by
        cases hlc : cb.last
        · obtain ⟨dn, h1, h2, h3⟩ := nbr_t hw.geo hc hlc
          exact ⟨dn, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨cb, fun h => by cases h⟩
      exact case_skip cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live o1 o2 o4
        hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H hw hl hc hdn hca hcaf hcbf
        (fun e => hab (by rw [e])) hcanf hcbnf hhead (by omega) (by omega) hfa
  · -------------------------------------------------------------- `CAN_MERGE` on `a`
    have hp0 : ca.prev ≠ 0 := by omega
    obtain ⟨d0, hd0, hd0a, hd0n, hd0l⟩ := hw.geo.prev_nb ca hca hp0
    obtain rfl : d0 = cb := mem_unique hnd hd0 hcb (by rw [hd0a, hcap])
    obtain ⟨s, t, hc⟩ := adjacent hw.geo hd0 hca hd0n hd0l
    have hb0 : 0 < d0.addr := by omega
    cases hlc : ca.last
    · obtain ⟨m, hm', hma, hmp⟩ := hw.geo.next_nb ca hca hlc
      obtain ⟨t', ht⟩ := next_head hw.geo (s := s ++ [d0]) (t := t) (by rw [hc]; simp) hm' hma.symm hlc
      have hc2 : (mergedM H s t d0 ca).cells = s ++ bM d0 ca :: { m with prev := d0.addr } :: t' := by
        simp only [mergedM, ht, hlc, Bool.false_eq_true, ↓reduceIte]
      exact case_merge cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live o1 o2 o4
        hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H hw hl hc hcbf hcaf hd0n hcbnf hhead hb0
        (wf_merged2 hw hc hcaf hcbf hcbnf hcap hp0 hlc ht hma hmp) hc2
        (fun _ => ⟨by simp, by simp [bM, hma], by simp [bM]⟩)
        (open_merge2 hw hc hcbf hcaf hd0n hd0l hcap hcanf hcbnf hlc ht hma hmp)
    · have hc2 : (mergedM H s t d0 ca).cells = s ++ bM d0 ca :: t := by
        cases t with
        | nil => rfl
        | cons m t' => simp only [mergedM, hlc, ↓reduceIte]
      exact case_merge cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live o1 o2 o4
        hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H hw hl hc hcbf hcaf hd0n hcbnf hhead hb0
        (wf_merged1 hw hc hcaf hcbf hcbnf hcap hp0 hlc) hc2 (d2 := d0)
        (fun h => by simp [bM, hlc] at h)
        (open_merge1 hw hc hcbf hcaf hd0n hd0l hcap hcanf hcbnf hlc d0)

end Dispatch

end WNear.Binary.AllocTwo
