import Bridge.Functions.AllocWalkRes

/-!
# `alloc_first_fit` (580) on a free list of any length (M4)

`AllocTwoF580` walks free lists of at most two cells. This file walks any list `heapInv … F`
allows, with the walk's two loops as loop invariants over the heap model (`AllocWalkModel`):

* `inv3`, at the head of the walk (`@3`): a model `H` (`H.wf live F`), the slot holding its
  head, its cells (`stW`), and `wc cfg L + 310` credits for its `L` listed cells;
* `inv7`, at the head of the merge loop (`@7`): the same with a nonempty list and `wc cfg L + 290`.

Each iteration of `@7` either merges the head (with `CAN_MERGE`) into its previous neighbour
(`merge7G`: the list one shorter, back to `@7`), or walks the head as `AllocTwoWalk.body7` does:
unlinked (the list one shorter, back to `@3`), taken whole, or split (the walk ends). Every
iteration that does not end the walk removes a listed cell, so the walk ends after at most `2F`
of them; `wc cfg L = 320 · L` `regular_op_cost`s pays for one merge and one unlink per cell.

* `merge7G`: the merge iteration;
* `body3G`: one iteration of `@3` at a nonempty list (the merge loop inside);
* `f580_walk`: 580 from `stW` on any model, at `walkCost cfg F`.
-/

namespace WNear.Binary.AllocWalk

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocLeaves WNear.Binary.AllocFirstFit
open WNear.Binary.AllocTwoWalk
open WNear.Binary.AllocSeqModel (mem_cells)
open WNear.Binary.AllocSeq (frO word0_free)
open WNear.Binary.AllocTwo (bM mergedM)
open WNear.Binary.AllocDealloc (nodup_of_sorted cellAt_iff' mem_unique memBytes_at)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocGen (walkQ)
set_option maxRecDepth 20000

/-! ## Credits and invariants -/

/-- The walk's credits for `L` listed cells: one merge and one unlink each. -/
def wc (cfg : WasmConfig) (L : Nat) : Nat := L * (320 * cfg.regularOpCost)

theorem wc_succ (cfg : WasmConfig) (L : Nat) : wc cfg (L + 1) = wc cfg L + 320 * cfg.regularOpCost := by
  unfold wc; rw [Nat.succ_mul]

theorem wc_mono (cfg : WasmConfig) {L L' : Nat} (h : L ≤ L') : wc cfg L ≤ wc cfg L' :=
  Nat.mul_le_mul_right _ h

/-- 580's cost on `heapInv … F`, activation excluded. -/
def walkCost (cfg : WasmConfig) (F : Nat) : Nat := wc cfg F + 330 * cfg.regularOpCost

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The walk's state: the model `H`, the slot holding its head, its cells, the policy's vtable
slot. -/
def stW (n : Nat) (live : List (Nat × Nat)) (F len slot : Nat) (idx : UInt32) (ta a578 : Nat)
    (H : HeapModel) : IProp GF :=
  iprop(⌜H.wf live F ∧ H.len = len⌝ ∗ n ↦[i32][ slot ] UInt32.ofNat H.head ∗
    ([∗list] c ∈ H.cells, cellRes n live c) ∗ vt n 1057464 idx ta a578)

/-- The invariant at the head of the walk (`@3`). -/
def inv3 (cfg : WasmConfig) (Cg R inst : Nat) (mi : ModuleInst) (n : Nat) (live : List (Nat × Nat))
    (F len : Nat) (w al slot idx : UInt32) (ta a578 : Nat) : List Value → Frame → IProp GF := fun X g =>
  iprop(⌜X = []⌝ ∗ ∃ (H : HeapModel) (l9 l10 l11 l12 l13 : UInt32),
    ⌜g = ⟨#[.i32 w, .i32 (UInt32.ofNat H.head), .i32 slot, .i32 1057464, .i32 1057464, .i32 0,
      .i32 (0 - al), .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩⌝ ∗
    credits Cg (wc cfg H.freeList.length + 310 * cfg.regularOpCost + R) ∗ stW n live F len slot.toNat idx ta a578 H)

/-- The invariant at the head of the merge loop (`@7`). -/
def inv7 (cfg : WasmConfig) (Cg R inst : Nat) (mi : ModuleInst) (n : Nat) (live : List (Nat × Nat))
    (F len : Nat) (w al slot idx : UInt32) (ta a578 : Nat) : List Value → Frame → IProp GF := fun X g =>
  iprop(⌜X = []⌝ ∗ ∃ (H : HeapModel) (l9 l10 l11 l12 l13 : UInt32),
    ⌜H.freeList ≠ [] ∧ g = ⟨#[.i32 w, .i32 (UInt32.ofNat H.head), .i32 slot, .i32 1057464, .i32 1057464, .i32 0,
      .i32 (0 - al), .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩⌝ ∗
    credits Cg (wc cfg H.freeList.length + 290 * cfg.regularOpCost + R) ∗ stW n live F len slot.toNat idx ta a578 H)

/-- The walk's failure: every listed cell unlinked (and leaked). -/
def zW (n : Nat) (live : List (Nat × Nat)) (F len : Nat) : IProp GF :=
  iprop(∃ H : HeapModel, ⌜H.wf live F ∧ H.len = len ∧ H.freeList = []⌝ ∗ [∗list] c ∈ H.cells, cellRes n live c)

/-- The walk's success: the block `r` (aligned) lent, the list's new head `v`. -/
def wW (n : Nat) (live : List (Nat × Nat)) (F len size : Nat) (al idx : UInt32) (ta a578 : Nat)
    (r v : UInt32) : IProp GF :=
  iprop(vt n 1057464 idx ta a578 ∗ ⌜r.toNat % al.toNat = 0⌝ ∗ heapW n live F len r.toNat size v)

end Defs

/-! ## The merge iteration -/

section Merge

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- The merge iteration of `@7` at the model `H`: the head `ca` (with `CAN_MERGE`) merged into its
previous neighbour `cb`, the next listed cell; `inv7` on the merged model. -/
theorem merge7G (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φ : Post NearState GF)
    (inst : Nat) (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (a575 a576 : Nat)
    (h575 : mi.funcAddrs[575]? = some a575) (h576 : mi.funcAddrs[576]? = some a576)
    (ty575 ty576 : FuncType)
    (hp575 : ty575.params.length = 1) (hr575 : ty575.results.length = 0)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot idx : UInt32) (ta a578 maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (H : HeapModel) (hw : H.wf live F) (hl : H.len = len)
    {s t : List CellM} {cb ca : CellM} {rest : List Nat} (hc : H.cells = s ++ cb :: ca :: t)
    (hfl : H.freeList = ca.addr :: cb.addr :: rest) (hcaf : ca.allocated = false) (hcbf : cb.allocated = false)
    (hcap : ca.prev = cb.addr) (hcanf : ca.nextFree = cb.addr + 1) (l9 l10 l11 l12 l13 : UInt32) :
    code575 inst mi a575 a576 ty575 ty576 ∗ n ↪[wmlimit] some maxP ∗
      credits Cg (wc cfg H.freeList.length + 290 * cfg.regularOpCost + R) ∗
      stW n live F len slot.toNat idx ta a578 H
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 (UInt32.ofNat H.head), .i32 slot, .i32 1057464, .i32 1057464, .i32 0,
            .i32 (0 - al), .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩
          [] l7Body (Post.mloop cfg Cg 0 [] (inv7 cfg Cg R inst mi n live F len w al slot idx ta a578) Φ) := by
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have hg := hw.geo
  have ba := hg.bounds ca hca
  have bb := hg.bounds cb hcb
  have hna := hg.next_al ca hca
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hm0 := hw.mem0_pos
  obtain ⟨dd, hdd, hdda, hddn, hddl⟩ := hg.prev_nb ca hca (by rw [hcap]; omega)
  obtain rfl : dd = cb := mem_unique (nodup_of_sorted hg.sorted) hdd hcb (by rw [hdda, hcap])
  have hcaN : (UInt32.ofNat ca.addr).toNat = ca.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcbN : (UInt32.ofNat dd.addr).toNat = dd.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcnN : (UInt32.ofNat ca.next).toNat = ca.next := by simp only [UInt32.toNat_ofNat']; omega
  have hhead : H.head = ca.addr := by simp [HeapModel.head, hfl]
  have hwm := wf_mergedG hw hc hfl hcaf hcbf hcap
  have hmhead : (mergedG H s t dd ca rest).head = dd.addr := by simp [HeapModel.head, mergedG]
  have hmlen : (mergedG H s t dd ca rest).freeList.length = rest.length + 1 := by simp [mergedG]
  have hwc : wc cfg H.freeList.length = wc cfg (rest.length + 1) + 320 * cfg.regularOpCost := by
    rw [hfl, List.length_cons, List.length_cons, wc_succ]
  have ha3 : UInt32.ofNat ca.addr &&& 3 = 0 := and3_of_mod4 _ (by rw [hcaN]; omega)
  have hb3 : UInt32.ofNat dd.addr &&& 3 = 0 := and3_of_mod4 _ (by rw [hcbN]; omega)
  have hnx3 : UInt32.ofNat ca.next &&& 3 = 0 := and3_of_mod4 _ (by rw [hcnN]; omega)
  have hb0 : 1 ≤ (UInt32.ofNat dd.addr).toNat := by rw [hcbN]; omega
  have hba : (UInt32.ofNat dd.addr).toNat + 12 ≤ (UInt32.ofNat ca.addr).toNat := by rw [hcbN, hcaN]; omega
  have han : (UInt32.ofNat ca.addr).toNat + 12 ≤ (UInt32.ofNat ca.next).toNat := by rw [hcaN, hcnN]; omega
  have hnx : (UInt32.ofNat ca.next).toNat + 65536 ≤ 2 ^ 32 := by rw [hcnN]; omega
  iintro ⟨#Hk5, #Hm, Hc, Hst⟩
  iunfold stW at Hst
  icases Hst with ⟨-, Hs, Hcs, Hvt⟩
  icases openMG (n := n) (maxP := maxP) hw hc hcbf hcaf hddn hddl hcap hcanf $$ [Hcs] with
    ⟨%bsa, %bsb, %tm, %dm, %⟨hla', hlb', hcm, hdm⟩, A0, A4, A8, Ad, B0, B8, Bd, Hn, Hfr⟩
  · iframe Hm Hcs
  ihave Hs := memBytes_at (b := slot.toNat) (bs' := bytes32 (UInt32.ofNat ca.addr)) rfl (by rw [hhead]) $$ Hs
  rw [hhead]
  mcredits (170 * cfg.regularOpCost + (wc cfg (rest.length + 1) + 290 * cfg.regularOpCost + R))
  iapply (merge7 cfg lim d Φ (inv7 cfg Cg R inst mi n live F len w al slot idx ta a578) inst mi n hn a575 a576
    h575 h576 ty575 ty576 hp575 hr575 hp576 hr576 hd Cg (wc cfg (rest.length + 1) + 290 * cfg.regularOpCost + R)
    w al slot 1057464 1057464 (UInt32.ofNat ca.addr) (UInt32.ofNat dd.addr) (UInt32.ofNat ca.next)
    l9 l10 l11 l12 l13 ca.last ha3 hb3 hnx3 hb0 hba han hnx)
  iframe Hk5 Hc Hs A0 A4 A8 B0 Hn
  iintro Hc Hs A0 A4 A8 B0 Hn
  simp only [inv7]
  isplitr; · ipureintro; trivial
  iexists mergedG H s t dd ca rest, UInt32.ofNat dd.addr, l10, l11, l12, l13
  isplitr
  · ipureintro; exact ⟨by simp [mergedG], by rw [hmhead]⟩
  rw [hmlen]
  iframe Hc
  iunfold stW
  isplitr; · ipureintro; exact ⟨hwm, hl⟩
  rw [hmhead]
  iframe Hs Hvt
  iapply closeMG (n := n) (maxP := maxP) hwm hcm hdm hcbf bsa bsb hla' hlb' (by omega)
  iframe Hfr B0 B8 Bd A0 A4 A8 Ad Hn

end Merge

/-! ## The walk's other steps, on the heap -/

section Steps

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocSeq (aN_al)

/-- The next listed cell (the `next_free` of a head without `CAN_MERGE`) is word-aligned. -/
theorem nf_al {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {a : Nat}
    {rest : List Nat} (hfl : H.freeList = a :: rest) : rest.headD 0 % 4 = 0 ∧ rest.headD 0 < 2 ^ 32 := by
  cases rest with
  | nil => simp
  | cons b rest' =>
    obtain ⟨x, hx, -⟩ := hw.lists.fl_free b (by rw [hfl]; simp)
    obtain ⟨hxm, hxa⟩ := (cellAt_iff' (nodup_of_sorted hw.geo.sorted)).mp hx
    have := hw.geo.bounds x hxm
    have := hw.len_lt
    simp only [List.headD_cons]; omega

variable {n maxP len : Nat} {live : List (Nat × Nat)} {F : Nat} {H : HeapModel} {s t : List CellM}
  {c d : CellM} {rest : List Nat}

/-- The head `c` unlinked (and leaked): `inv3` on the list's tail. -/
theorem unlink3 (cfg : WasmConfig) (Cg R inst : Nat) (mi : ModuleInst) (w al slot idx : UInt32) (ta a578 : Nat)
    (hw : H.wf live F) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
    (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr) (hcf : c.allocated = false)
    (hfl : H.freeList = c.addr :: rest) (hnf : c.nextFree = rest.headD 0)
    (bs : List UInt8) (hbs : bs.length + 12 + c.addr = c.next) (l9 l10 l11 l12 l13 : UInt32) :
    credits Cg (wc cfg rest.length + 310 * cfg.regularOpCost + R) ∗ frO (GF := GF) n maxP live s t c d ∗
      n ↦[i32][ slot.toNat ] UInt32.ofNat c.nextFree ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] w0 (UInt32.ofNat c.next) c.last ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗
      n ↦[i32][ 1057480 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578
      ⊢ inv3 cfg Cg R inst mi n live F len w al slot idx ta a578 []
          ⟨#[.i32 w, .i32 (UInt32.ofNat c.nextFree), .i32 slot, .i32 1057464, .i32 1057464, .i32 0, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ := by
  have hhd : ({ H with freeList := rest } : HeapModel).head = c.nextFree := by
    simp [HeapModel.head, hnf]
  iintro ⟨Hc, Hfr, Hs, H0, H8, Hd, Hn, Hv, Ht⟩
  simp only [inv3]
  isplitr; · ipureintro; trivial
  iexists { H with freeList := rest }, l9, l10, l11, l12, l13
  rw [hhd, show ({ H with freeList := rest } : HeapModel).freeList = rest from rfl]
  isplitr; · ipureintro; rfl
  iframe Hc
  iunfold stW
  isplitr; · ipureintro; exact ⟨wf_tail hw hfl, hl⟩
  rw [hhd]
  iframe Hs
  isplitr [Hv Ht]
  · iapply close_oneW (n := n) (maxP := maxP) hw hc hd hcf bs hbs
    iframe Hfr H0 H8 Hd Hn
  · ihave Hv := memBytes_addr (a := 1057480) (b := (1057464 : UInt32).toNat + 16) rfl $$ Hv
    iunfold vt; iframe Hv Ht

/-- The head `c` taken whole: the walk's success. -/
theorem whole3 (w al slot idx : UInt32) (ta a578 size : Nat) (args : List Value)
    (hw : H.wf live F) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
    (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr) (hcf : c.allocated = false)
    (hfl : H.freeList = c.addr :: rest) (hnf : c.nextFree = rest.headD 0)
    (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (hfit : fits w (UInt32.ofNat c.addr) (UInt32.ofNat c.next)) (hali : aligned al (UInt32.ofNat c.addr))
    (bs : List UInt8) (hbs : bs.length + 12 + c.addr = c.next) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[i32][ slot.toNat ] UInt32.ofNat c.nextFree ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗
      n ↦[i32][ 1057480 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578
      ⊢ walkQ n slot.toNat idx ta a578 (zW n live F len) (wW n live F len size al idx ta a578) args
          [.i32 (UInt32.ofNat c.addr + 8)] := by
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hw.geo.bounds c hcc
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnN : (UInt32.ofNat c.next).toNat = c.next := by simp only [UInt32.toNat_ofNat']; omega
  have hp : (UInt32.ofNat c.addr + 8).toNat = c.addr + 8 := by
    rw [UInt32.toNat_add, hcN]; simp; omega
  have hfit' : 4 * w.toNat ≤ c.next - c.addr - 8 := by unfold fits szN at hfit; rw [hcN, hnN] at hfit; exact hfit
  iintro ⟨Hfr, Hs, H0, H8, Hd, Hn, Hv, Ht⟩
  iunfold walkQ
  iexists UInt32.ofNat c.addr + 8
  isplitr; · ipureintro; rfl
  iright
  isplitr
  · ipureintro; intro h; have := congrArg UInt32.toNat h; rw [hp] at this; simp at this
  iexists UInt32.ofNat c.nextFree
  iframe Hs
  iunfold wW
  isplitl [Hv Ht]
  · ihave Hv := memBytes_addr (a := 1057480) (b := (1057464 : UInt32).toNat + 16) rfl $$ Hv
    iunfold vt; iframe Hv Ht
  isplitr
  · ipureintro; unfold aligned at hali; rw [hp]; rw [hcN] at hali; exact hali
  iapply packWG (n := n) (maxP := maxP) hw hl hc hd hcf hfl hnf w _ hp hfit' hs0 hsw bs hbs
  iframe Hfr H0 H8 Hd Hn

/-- The head `c` split at `A - 8`: the walk's success. -/
theorem split3 (w al slot idx A : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (ta a578 size : Nat)
    (args : List Value)
    (hw : H.wf live F) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
    (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr) (hcf : c.allocated = false)
    (hfl : H.freeList = c.addr :: rest) (hw1 : 1 ≤ w.toNat) (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (hA : A.toNat = aN (UInt32.ofNat c.next) w al)
    (hfit : fits w (UInt32.ofNat c.addr) (UInt32.ofNat c.next))
    (hsp : canSplit w al (UInt32.ofNat c.addr) (UInt32.ofNat c.next))
    (bs : List UInt8) (hbs : bs.length + 12 + c.addr = c.next) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[i32][ slot.toNat ] UInt32.ofNat c.addr ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (A - 8) ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs.take (A.toNat - 8 - (UInt32.ofNat c.addr).toNat - 12) ∗
      n ↦[i32][ (A - 8).toNat ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ A.toNat - 4 ] UInt32.ofNat c.addr ∗
      (∃ bs' : List UInt8, ⌜bs'.length = (UInt32.ofNat c.next).toNat - A.toNat⌝ ∗ n ↦[wms][ A.toNat ] bs') ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr &&& 3 ||| (A - 8)) c.last ∗
      n ↦[i32][ 1057480 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a578
      ⊢ walkQ n slot.toNat idx ta a578 (zW n live F len) (wW n live F len size al idx ta a578) args
          [.i32 A] := by
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hw.geo.bounds c hcc
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hm0 := hw.mem0_pos
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnN : (UInt32.ofNat c.next).toNat = c.next := by simp only [UInt32.toNat_ofNat']; omega
  have hfit' : 4 * w.toNat ≤ c.next - c.addr - 8 := by unfold fits szN at hfit; rw [hcN, hnN] at hfit; exact hfit
  have hcs : c.addr + 80 ≤ A.toNat := by unfold canSplit at hsp; rw [hcN, ← hA] at hsp; exact hsp
  have eNN : (A - 8).toNat = A.toNat - 8 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
  iintro ⟨Hfr, Hs, H0, H8, Hd, HNa, HNb, HB, Hn, Hv, Ht⟩
  ihave HNa := memBytes_addr eNN $$ HNa
  iunfold walkQ
  iexists A
  isplitr; · ipureintro; rfl
  iright
  isplitr
  · ipureintro; intro h; rw [h] at hcs; simp at hcs
  iexists UInt32.ofNat c.addr
  iframe Hs
  iunfold wW
  isplitl [Hv Ht]
  · ihave Hv := memBytes_addr (a := 1057480) (b := (1057464 : UInt32).toNat + 16) rfl $$ Hv
    iunfold vt; iframe Hv Ht
  isplitr
  · ipureintro; rw [hA]; exact aN_al _ _ _
  iapply packSG (n := n) (maxP := maxP) hw hl hc hd hcf hfl w al A k hal (by omega) hA hfit' hcs hw1 hs0 hsw bs hbs
  iframe Hfr H0 H8 Hd HNa HNb HB Hn

end Steps

/-! ## One iteration of the walk -/

section Body

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `AllocTwoWalk.exitW` with the continuation unfolded, as the control steps leave it. -/
theorem exitW' (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φf : Post NearState GF) (inst : Nat)
    (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat)
    (w al slot pd pv c v s x l5 l10 l11 l12 l13 : UInt32) (hc : c.toNat + 12 < 2 ^ 32) :
    credits Cg (30 * cfg.regularOpCost + R) ∗ n ↦[i32][ slot.toNat ] s ∗ n ↦[i32][ c.toNat ] x ∗
      n ↦[i32][ c.toNat + 8 ] v ∗
      (∀ g, credits Cg R -∗ n ↦[i32][ slot.toNat ] (v &&& 4294967292) -∗ n ↦[i32][ c.toNat ] (x ||| 1) -∗
        n ↦[i32][ c.toNat + 8 ] v -∗ Φf.normal [.i32 (c + 8)] g)
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 c, .i32 slot, .i32 pd, .i32 pv, .i32 l5, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 (c + 8), .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩ [] yRest
          (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d xRest
            (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d [Instr.local_get 5] Φf)))) := by
  have h := exitW cfg lim d Φf inst mi n hn Cg R w al slot pd pv c v s x l5 l10 l11 l12 l13 hc
  unfold postY at h
  simp only [Post.mseq_normal, List.nil_append] at h
  exact h

/-- `AllocTwoWalk.exitS` with the continuation unfolded, as the control steps leave it. -/
theorem exitS' (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (Φf : Post NearState GF) (inst : Nat)
    (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat)
    (w al c l2 pd pv N l5 nx l12 l13 x : UInt32) :
    credits Cg (30 * cfg.regularOpCost + R) ∗ n ↦[i32][ N.toNat ] x ∗
      (∀ g, credits Cg R -∗ n ↦[i32][ N.toNat ] (x ||| 1) -∗ Φf.normal [.i32 (N + 8)] g)
      ⊢ (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d xRest
            (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d [Instr.local_get 5] Φf)))).br 0 []
          ⟨#[.i32 w, .i32 c, .i32 l2, .i32 pd, .i32 pv, .i32 l5, .i32 (0 - al),
            .i32 (al + 4294967295), .i32 0, .i32 N, .i32 nx, .i32 nx, .i32 l12, .i32 l13], inst, mi⟩ := by
  have h := exitS cfg lim d Φf inst mi n hn Cg R w al c l2 pd pv N l5 nx l12 l13 x
  unfold postY at h
  simp only [Post.mseq_br] at h
  exact h

/-- 580's own postcondition after the walk: the result `walkQ`, the credits `R` left. -/
abbrev postW (cfg : WasmConfig) (lim : ExecLimits) (d Cg R n : Nat) (live : List (Nat × Nat)) (F len size : Nat)
    (al slot idx : UInt32) (ta a578 : Nat) (args : List Value) : Post NearState GF :=
  postY cfg lim d Cg (Post.mfunc cfg Cg 1
    { ret := fun rs => iprop(credits Cg R ∗ walkQ n slot.toNat idx ta a578 (zW n live F len) (wW n live F len size al idx ta a578) args rs) })

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- One iteration of the walk (`@3`) at a nonempty list: the merge loop (`@7`, `inv7`) merges
(`merge7G`) until the head has no `CAN_MERGE`, which is then unlinked (`inv3` on the tail), taken
whole or split (the walk's success). -/
theorem body3G (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (inst : Nat) (mi : ModuleInst) (n : Nat) (hn : mi.memAddrs[0]? = some n) (a572 a575 a576 a574 a578 ta : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h575 : mi.funcAddrs[575]? = some a575)
    (h576 : mi.funcAddrs[576]? = some a576)
    (h574 : mi.funcAddrs[574]? = some a574) (hta : mi.tableAddrs[0]? = some ta)
    (ty572 ty575 ty576 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp575 : ty575.params.length = 1) (hr575 : ty575.results.length = 0)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hty578 : (mi.types[13]!).params.length = 2) (hrt578 : (mi.types[13]!).results.length = 1)
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (w al slot idx : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hk : k ≤ 20)
    (hw1 : 1 ≤ w.toNat) (hw2 : w.toNat < 2 ^ 28)
    (maxP len : Nat) (live : List (Nat × Nat)) (F size : Nat) (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (args : List Value) (H : HeapModel) (hne : H.freeList ≠ []) (l9 l10 l11 l12 l13 : UInt32) :
    code7 (GF := GF) inst mi a572 a576 a574 a578 ty572 ty576 ty574 ∗ code575 inst mi a575 a576 ty575 ty576 ∗
      n ↪[wmlimit] some maxP ∗
      credits Cg (wc cfg H.freeList.length + 310 * cfg.regularOpCost + R) ∗
      stW n live F len slot.toNat idx ta a578 H
      ⊢ mwpi cfg lim d ⟨#[.i32 w, .i32 (UInt32.ofNat H.head), .i32 slot, .i32 1057464, .i32 1057464, .i32 0,
            .i32 (0 - al), .i32 (al + 4294967295), .i32 0, .i32 l9, .i32 l10, .i32 l11, .i32 l12, .i32 l13], inst, mi⟩
          [] l3Body (Post.mloop cfg Cg 0 [] (inv3 cfg Cg R inst mi n live F len w al slot idx ta a578)
            (postW cfg lim d Cg R n live F len size al slot idx ta a578 args)) := by
  iintro ⟨#Hk, #Hk5, #Hm, Hc, Hst⟩
  iunfold stW at Hst
  icases Hst with ⟨%⟨hw, hl⟩, Hs, Hcs, Hvt⟩
  obtain ⟨a, rest, hfl⟩ : ∃ a rest, H.freeList = a :: rest := by
    cases h : H.freeList with
    | nil => exact absurd h hne
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hne0 : UInt32.ofNat H.head ≠ 0 := by
    obtain ⟨ca, hca, -, -, -⟩ := head_facts hw hfl
    obtain ⟨hcam, hcaa⟩ := (cellAt_iff' (nodup_of_sorted hw.geo.sorted)).mp hca
    have hb := hw.geo.bounds ca hcam
    have hm0 := hw.mem0_pos
    have hlt := hw.len_lt
    have ha : (UInt32.ofNat H.head).toNat = a := by
      simp only [HeapModel.head, hfl, List.headD_cons, UInt32.toNat_ofNat']; omega
    intro h; rw [h] at ha; simp at ha; omega
  mstep; mstep
  mstep_not_taken with (exact eqz_false _ hne0)
  mstep; mstep; mstep
  mcredits (cfg.regularOpCost + (wc cfg H.freeList.length + 290 * cfg.regularOpCost + R))
  iapply WNear.Binary.MemCpy.mwpi_loop0 (Cg := Cg) (R := wc cfg H.freeList.length + 290 * cfg.regularOpCost + R)
    .empty _ (inv7 cfg Cg R inst mi n live F len w al slot idx ta a578) rfl
  isplitr
  swap
  · isplitl [Hc]; · iexact Hc
    inext; iintro Hc
    simp only [inv7]
    isplitr; · ipureintro; trivial
    iexists H, l9, l10, l11, l12, l13
    isplitr; · ipureintro; exact ⟨hne, rfl⟩
    iframe Hc
    iunfold stW
    iframe Hs Hcs Hvt
    ipureintro; exact ⟨hw, hl⟩
  imodintro
  iintro %X %l HI
  iunfold inv7 at HI
  icases HI with ⟨%hX, %H', %m9, %m10, %m11, %m12, %m13, %⟨hne', hg⟩, Hc, Hst⟩
  subst hX
  rw [hg]
  clear hfl hw hl hne hne0
  iunfold stW at Hst
  icases Hst with ⟨%⟨hw', hl'⟩, Hs, Hcs, Hvt⟩
  obtain ⟨a', rest', hfl'⟩ : ∃ a rest, H'.freeList = a :: rest := by
    cases h : H'.freeList with
    | nil => exact absurd h hne'
    | cons a rest => exact ⟨a, rest, rfl⟩
  obtain ⟨ca', hca', hcaf', hnf0, hnf1⟩ := head_facts hw' hfl'
  obtain ⟨hcam', hcaa'⟩ := (cellAt_iff' (nodup_of_sorted hw'.geo.sorted)).mp hca'
  subst hcaa'
  have hhead : H'.head = ca'.addr := by simp [HeapModel.head, hfl']
  by_cases hodd : ca'.nextFree % 2 = 1
  · ---------------------------------------------------------------- merge
    obtain ⟨cb, rest'', hrest, hcb, hcbf, hcap, hcanf⟩ := hnf1 hodd
    subst hrest
    obtain ⟨s0, t0, hc0⟩ := List.append_of_mem hcam'
    have hcbm := ((cellAt_iff' (nodup_of_sorted hw'.geo.sorted)).mp hcb).1
    have hb' := hw'.geo.bounds cb hcbm
    have hm0' := hw'.mem0_pos
    obtain ⟨dd, hdd, hdda, hddn, -⟩ := hw'.geo.prev_nb ca' hcam' (by rw [hcap]; omega)
    obtain rfl : dd = cb := mem_unique (nodup_of_sorted hw'.geo.sorted) hdd hcbm (by rw [hdda, hcap])
    obtain ⟨s, hc⟩ := prev_split hw'.geo hc0 hcbm hddn
    iapply (merge7G cfg lim d _ inst mi n hn a575 a576 h575 h576 ty575 ty576 hp575 hr575 hp576 hr576 hd Cg R
      w al slot idx ta a578 maxP len live F H' hw' hl' hc hfl' hcaf' hcbf hcap hcanf m9 m10 m11 m12 m13)
    iframe Hk5 Hm Hc
    iunfold stW
    iframe Hs Hcs Hvt
    ipureintro; exact ⟨hw', hl'⟩
  ---------------------------------------------------------------- no merge
  have hnf : ca'.nextFree = rest'.headD 0 := hnf0 (by omega)
  obtain ⟨s, t, hc⟩ := List.append_of_mem hcam'
  obtain ⟨d', hd'⟩ := nbr_any hw'.geo hc
  have hb' := hw'.geo.bounds ca' hcam'
  have hna := hw'.geo.next_al ca' hcam'
  have hlt' := hw'.len_lt
  have hla' := hw'.len_al
  have hm0' := hw'.mem0_pos
  obtain ⟨hnfa, hnfl⟩ := nf_al hw' hfl'
  have hcaN : (UInt32.ofNat ca'.addr).toNat = ca'.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcnN : (UInt32.ofNat ca'.next).toNat = ca'.next := by simp only [UInt32.toNat_ofNat']; omega
  have hvN : (UInt32.ofNat ca'.nextFree).toNat = ca'.nextFree := by simp only [UInt32.toNat_ofNat']; omega
  have hv3 : UInt32.ofNat ca'.nextFree &&& 3 = 0 := and3_of_mod4 _ (by rw [hvN]; omega)
  have hc0 : 1 ≤ (UInt32.ofNat ca'.addr).toNat := by rw [hcaN]; omega
  have hnx4 : UInt32.ofNat ca'.next &&& 3 = 0 := and3_of_mod4 _ (by rw [hcnN]; omega)
  have hcnx : (UInt32.ofNat ca'.addr).toNat + 12 ≤ (UInt32.ofNat ca'.next).toNat := by rw [hcaN, hcnN]; omega
  have hnx : (UInt32.ofNat ca'.next).toNat + 65536 ≤ 2 ^ 32 := by rw [hcnN]; omega
  have hwc : wc cfg H'.freeList.length = wc cfg rest'.length + 320 * cfg.regularOpCost := by
    rw [hfl', List.length_cons, wc_succ]
  have e8 : (UInt32.ofNat ca'.addr + 8).toNat = (UInt32.ofNat ca'.addr).toNat + 8 := by
    rw [UInt32.toNat_add]; simp; omega
  icases open_oneW (n := n) (maxP := maxP) hw' hc hd' hcaf' $$ [Hcs] with ⟨%bs, %hbs, H0, H8, Hd, Hn, Hfr⟩
  · iframe Hm Hcs
  have hbs' : bs.length + 12 + (UInt32.ofNat ca'.addr).toNat = (UInt32.ofNat ca'.next).toNat := by
    rw [hcaN, hcnN]; omega
  iunfold vt at Hvt
  icases Hvt with ⟨Hv, Ht⟩
  ihave Hs := memBytes_at (b := slot.toNat) (bs' := bytes32 (UInt32.ofNat ca'.addr)) rfl (by rw [hhead]) $$ Hs
  rw [hhead]
  mcredits (279 * cfg.regularOpCost + (8 * cfg.regularOpCost + (wc cfg rest'.length + 310 * cfg.regularOpCost + R)))
  iapply (body7 cfg lim d _ _ inst mi n hn a572 a576 a574 a578 ta h572 h576 h574 hta ty572 ty576 ty574
    hp572 hr572 hp576 hr576 hp574 hr574 hty578 hrt578 hd Cg
    (8 * cfg.regularOpCost + (wc cfg rest'.length + 310 * cfg.regularOpCost + R))
    w al slot 1057464 1057464 idx (UInt32.ofNat ca'.addr) (UInt32.ofNat ca'.next) (UInt32.ofNat ca'.addr)
    (UInt32.ofNat ca'.nextFree) m9 m10 m11 m12 m13 ca'.last bs k hal hk hw1 hw2 hc0 hnx4 hv3 hcnx hnx hbs'
    (279 * cfg.regularOpCost) (by split <;> omega))
  iframe Hk Hc
  isplitl [H0 H8 Hd Hn Hv Ht]
  · iunfold cellW; iframe H0 H8 Hd Hn Hv Ht
  isplit
  · -- too small: unlinked
    iintro %hfit Hc HR
    simp only [Post.mblock_br_succ, Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
    mctrl_norm
    mpay
    iunfold cellW at HR
    icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
    mstep; mstep; mstep [H8]; mstep; mstep [Hs]
    iapply mwpi_br
    simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
    iapply pure_pay_intro'
    isplitl [Hc]; · iexact Hc
    isplitr; · ipureintro; exact ⟨by simp, by omega⟩
    inext; iintro Hc
    simp only [List.length_nil, List.drop_nil]
    mcredits (wc cfg rest'.length + 310 * cfg.regularOpCost + R)
    iapply (unlink3 cfg Cg R inst mi w al slot idx ta a578 hw' hl' hc hd' hcaf' hfl' hnf bs hbs _ _ _ _ _)
    iframe Hc Hfr Hs H0 H8 Hd Hn Hv Ht
  isplit
  · -- not splittable: the alignment
    iintro %⟨hfit, hsplit⟩ Hc HR
    simp only [Post.mblock_br_zero, Post.mseq_normal, List.nil_append]
    mctrl_norm
    mpay
    mstep; mstep; mstep; mstep
    by_cases hali : aligned al (UInt32.ofNat ca'.addr)
    · have hbr := eqz_and_true (UInt32.ofNat ca'.addr + 8) al k hal hk (by rw [e8]; exact hali)
      iapply mwpi_cons
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, hbr⟩
      clear hbr
      simp only [List.reverse_nil, Post.mseq_br, Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero,
        List.nil_append]
      mpay
      simp only [Post.mloop_normal, List.nil_append]
      mpay
      iunfold cellW at HR
      icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
      iapply (exitW' cfg lim d _ inst mi n hn Cg R w al slot 1057464 1057464 (UInt32.ofNat ca'.addr)
        (UInt32.ofNat ca'.nextFree) (UInt32.ofNat ca'.addr) (w0 (UInt32.ofNat ca'.next) ca'.last) 0 _ _ _ _
        (by omega))
      isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
      iframe Hs H0 H8
      iintro %g Hc Hs H0 H8
      rw [v_and3m _ hv3]
      mstep_post
      iframe Hc
      iapply (whole3 w al slot idx ta a578 size args hw' hl' hc hd' hcaf' hfl' hnf hs0 hsw hfit hali bs hbs)
      iframe Hfr Hs H0 H8 Hd Hn Hv Ht
    · have hbr := eqz_and_false (UInt32.ofNat ca'.addr + 8) al k hal hk (by rw [e8]; exact hali)
      mstep_not_taken with (exact hbr)
      clear hbr
      iunfold cellW at HR
      icases HR with ⟨H0, H8, Hd, Hn, Hv, Ht⟩
      mstep; mstep; mstep [H8]; mstep; mstep [Hs]
      iapply mwpi_br
      simp only [Post.mblock_br_succ, Post.mloop_br_succ, Post.mblock_br_zero, Post.mloop_br_zero, List.nil_append]
      iapply pure_pay_intro'
      isplitl [Hc]; · iexact Hc
      isplitr; · ipureintro; exact ⟨by simp, by omega⟩
      inext; iintro Hc
      simp only [List.length_nil, List.drop_nil]
      mcredits (wc cfg rest'.length + 310 * cfg.regularOpCost + R)
      iapply (unlink3 cfg Cg R inst mi w al slot idx ta a578 hw' hl' hc hd' hcaf' hfl' hnf bs hbs _ _ _ _ _)
      iframe Hc Hfr Hs H0 H8 Hd Hn Hv Ht
  · -- split
    iintro %A %l2 %⟨hA1, hfit, hsp⟩ Hc HS Hv Ht
    simp only [Post.mblock_br_succ, Post.mseq_br, Post.mloop_br_succ, List.nil_append]
    have hA80 : (UInt32.ofNat ca'.addr).toNat + 80 ≤ A.toNat := by unfold canSplit at hsp; omega
    ihave HS := split_post n (UInt32.ofNat ca'.addr) (UInt32.ofNat ca'.next) (UInt32.ofNat ca'.addr) A
      (UInt32.ofNat ca'.nextFree) ca'.last bs hA80 $$ HS
    icases HS with ⟨H0, H8, Hd, HNa, HNb, HN4r, Hn⟩
    have eNN : (A - 8).toNat = A.toNat - 8 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
    have hA8 : UInt32.ofNat (A.toNat - 8) = A - 8 := by
      apply UInt32.toNat_inj.mp; rw [eNN]; have := A.toNat_lt; simp only [UInt32.toNat_ofNat']; omega
    rw [hA8]
    iapply (exitS' cfg lim d _ inst mi n hn Cg R w al (UInt32.ofNat ca'.addr) l2 1057464 1057464 (A - 8) 0
      (UInt32.ofNat ca'.next) _ _ _)
    isplitl [Hc]; · mcredits (30 * cfg.regularOpCost + R); iexact Hc
    iframe HNa
    iintro %g Hc HNa
    rw [show A - 8 + 8 = A by simp]
    mstep_post
    iframe Hc
    rw [show A.toNat - (8 + (UInt32.ofNat ca'.addr).toNat + 12) = A.toNat - 8 - (UInt32.ofNat ca'.addr).toNat - 12 by omega]
    iapply (split3 w al slot idx A k hal ta a578 size args hw' hl' hc hd' hcaf' hfl' hw1 hs0 hsw hA1 hfit hsp bs hbs)
    iframe Hfr Hs H0 H8 Hd HNa HNb HN4r Hn Hv Ht

end Body

end WNear.Binary.AllocWalk
