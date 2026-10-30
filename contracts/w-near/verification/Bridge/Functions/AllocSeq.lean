import Bridge.Functions.AllocSeqPack

/-!
# `__rust_alloc` on the heap any sequence of allocations leaves (M4)

`f310_spec_seq`: `__rust_alloc(size, align)` from `heapInv n maxP len live 1` (so from any
`F ≤ 1`, by `heapInv_mono`) gives back `heapInv … 1`: an allocation without frees leaves a
free list of at most one cell, and `heapInv … 1` already says that cell has `next_free = 0`
(`AllocSeqModel.one_cell`), the list `f580_one` walks. So any sequence of allocations without
frees is covered by induction, starting from `heapInv_init` (`F = 0`).

```
{ ⌜args = [size, al]⌝ ∗ g_sp ↦ sp ∗ 581's 3 stack words ∗ vt ∗ heapInv n maxP len live 1 }
__rust_alloc(size, align)            cost 15 + 15 + 910 + grow(P)   (n ↪[wmlimit] some maxP held)
{ ∃ p, rs = [p] ∗ g_sp ↦ sp ∗ 3 stack words ∗ vt ∗ allocOutS n maxP len E live size al p P }

allocOutS =  (p ≠ 0 ∧ p % al = 0) ∗ ∃ len' ∈ {len, E}, heapInv n maxP len' ((p, size) :: live) 1 ∗ block p size
          ∨  (p = 0 ∧ (¬ GrowOk len (some maxP) P ∨ 8 < al)) ∗ ∃ len' ∈ {len, E}, heapInv n maxP len' live 1
```

`P = cellPages (wordsOf size) al`, `E = len + P · 65536`. The model at entry decides the
first walk (`AllocGen.f310_gen`'s `walkSpec`):

* head 0 (empty list, or a listed cell at address 0): `f580_empty`, the heap kept aside as
  `AllocFresh.frameH` (the list emptied);
* head `a ≠ 0`: the list is `[a]`, the cell `c` at `a` has `next_free = 0`; with the cells
  `s ++ c :: t` and `d` its next neighbour, `f580_one` on `c` (`oneRes`), the rest kept
  aside as `frO`. Whole → `packWO`, split → `packSO`, unlinked → `c` leaked (`restoreO`)
  and the grow path.

`f310_spec_room`: under `E / 65536 ≤ maxP` (room under the limit; `E + 65536 ≤ 2^32` is
already a premise) and `align ≤ 8`, the result is a block: `p ≠ 0`, aligned, `heapInv … 1`.
-/

namespace WNear.Binary.AllocSeq

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeqModel
open WNear.Binary.AllocFirstFit (post1 vt w0 aN fits canSplit aligned szN oneRes nextW f580_empty f580_one
  and3_of_mod4)
open WNear.Binary.AllocDealloc (cellRes_free memBytes_at nodup_of_sorted cellAt_iff')
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq cellPages)
open WNear.Binary.AllocFresh (frameH MFunSpec_frame)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocGen (walkQ walkSpec res581G pre581G f310_gen MFunSpec_cost MFunSpec_exists)
open WNear.Binary.AllocLimit (growOk_of_room)
open WNear.Binary.Interface (IfaceMod)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition with the heap's model `H` out. -/
def preX (n g : Nat) (gt : GlobalType) (sp : UInt32) (o1 o2 o4 : List UInt8) (idx : UInt32) (ta a578 maxP : Nat)
    (live : List (Nat × Nat)) (size al : UInt32) (H : HeapModel) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ sp.toNat - 16 ] o1 ∗
    n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ 1074896 ] UInt32.ofNat H.head ∗ n ↦[wmlength] H.len ∗ n ↪[wmlimit] some maxP ∗
    [∗list] c ∈ H.cells, cellRes n live c)

/-- The first walk's resources on the one-cell list `[c]` (`oneRes` but the slot). -/
def pwO (n : Nat) (c : CellM) (bs : List UInt8) (idx : UInt32) (ta a578 : Nat) : IProp GF :=
  iprop(n ↦[i32][ (UInt32.ofNat c.addr).toNat ] w0 (UInt32.ofNat c.next) c.last ∗
    n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] 0 ∗ n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
    nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗ vt n 1057464 idx ta a578)

/-- `f310_spec_seq`'s postcondition. -/
abbrev postS (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) : List Value → List Value → IProp GF :=
  fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    vt n 1057464 idx ta a578 ∗
    allocOutS n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
      (cellPages (wordsOf size) al).toNat)

/-- `AllocGen.f310_gen`'s postcondition. -/
abbrev postG (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 len maxP : Nat)
    (Z : IProp GF) (W : UInt32 → UInt32 → IProp GF) : List Value → List Value → IProp GF :=
  fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581G n g gt sp size al idx ta a578 len maxP Z W p)

/-- 581's success on `[c]`, packed. -/
theorem packOK {n maxP len : Nat} {live : List (Nat × Nat)} {H : HeapModel} {s t : List CellM} {c d : CellM}
    (hw : H.wf live 1) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
    (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr)
    (hfl : H.freeList = [c.addr]) (hcf : c.allocated = false) (hnf : c.nextFree = 0) (ha0 : 0 < c.addr)
    (size al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (bs : List UInt8) (hbs : bs.length + 4 = c.size) (idx : UInt32) (ta a578 E P : Nat) (p v : UInt32)
    (hp : p ≠ 0) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗
      AllocSeq.wO n (wordsOf size) al c bs idx ta a578 p v ⊢
      vt n 1057464 idx ta a578 ∗ allocOutS n maxP len E live size.toNat al p P := by
  have hg := hw.geo
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hg.bounds c hcc
  have hlt := hw.len_lt
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnN : (UInt32.ofNat c.next).toNat = c.next := by simp only [UInt32.toNat_ofNat']; omega
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  iintro ⟨HF, Hh, Hl, HW⟩
  ihave Hh := memBytes_addr (a := 1074896) (b := (1074896 : UInt32).toNat) rfl $$ Hh
  iunfold AllocSeq.wO at HW
  ihave HP := HW $$ Hh
  iunfold post1 at HP
  icases HP with ⟨%r, %hrs, Hvt, HP⟩
  obtain rfl : p = r := by simpa using hrs
  iframe Hvt
  iunfold allocOutS
  icases HP with (⟨%hU, -⟩ | ⟨%hWh, Hs, H0, H8, Hd, Hn⟩ | ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, Hn⟩)
  · exact absurd hU.1 hp
  · obtain ⟨hp', hfit, -, hali⟩ := hWh
    have hpn : p.toNat = c.addr + 8 := by
      rw [hp', UInt32.toNat_add, hcN, show (8 : UInt32).toNat = 8 from rfl]; omega
    have hfit' : 4 * (wordsOf size).toNat ≤ c.next - c.addr - 8 := by
      unfold fits szN at hfit; rw [hcN, hnN] at hfit; exact hfit
    ileft
    isplitr
    · ipureintro
      refine ⟨hp, ?_⟩
      unfold aligned at hali; rw [hcN] at hali; rw [hpn]; exact hali
    iexists len
    isplitr
    · ipureintro; exact Or.inl rfl
    iapply packWO hw hl hc hd hcf (wordsOf size) al p hpn hfit' (size := size.toNat) (by omega)
      (by rw [hW]; omega) bs hbs
    iframe HF Hl Hs H0 H8 Hd Hn
  · obtain ⟨hp', hfit, hcs⟩ := hS
    have hfit' : 4 * (wordsOf size).toNat ≤ c.next - c.addr - 8 := by
      unfold fits szN at hfit; rw [hcN, hnN] at hfit; exact hfit
    have hcs' : c.addr + 80 ≤ p.toNat := by unfold canSplit at hcs; rw [hcN, ← hp'] at hcs; exact hcs
    ileft
    isplitr
    · ipureintro; exact ⟨hp, by rw [hp']; exact aN_al _ _ _⟩
    iexists len
    isplitr
    · ipureintro; exact Or.inl rfl
    iapply packSO hw hl hc hd hfl hcf hnf (wordsOf size) al p k hal ha0 hp' hfit' hcs'
      (by rw [hW]; omega) (size := size.toNat) (by omega) (by rw [hW]; omega) bs hbs
    iframe HF Hl Hs H0 H8 Hd HN0 HN1 HB Hn

set_option maxHeartbeats 4000000 in
/-- `__rust_alloc(size, align)` (310 → 236 → 581) on the heap any sequence of allocations
leaves (`heapInv … 1`), holding the memory's limit (see the module doc). -/
theorem f310_spec_seq (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    n ↪[wmlimit] some maxP ∗
      A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)))
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          allocOutS n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
            (cellPages (wordsOf size) al).toNat)) := by
  iintro ⟨#Hm, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  -- the model out
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ x : {H : HeapModel // H.wf live 1 ∧ H.len = len},
      preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al x.1 args))
    (Q := postS n g gt sp size al idx ta (A 578) maxP len live) ?hP1 ?hQ1)
  case hP1 =>
    intro args
    iintro ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
    iunfold heapInv at Hinv
    icases Hinv with ⟨%H, %⟨hw, hl⟩, Hh, Hl, #Hlim, Hc⟩
    isplitl
    · iexists ⟨H, hw, hl⟩
      iunfold preX
      ihave Hh := memBytes_addr (a := headAddr) (b := 1074896) rfl $$ Hh
      iframe Hg Ho1 Ho2 Ho4 Hvt Hh Hl Hlim Hc
      ipureintro; exact ha
    · iempintro
  case hQ1 => intro args rs; iintro ⟨-, H⟩; iexact H
  iapply MFunSpec_exists
  imodintro
  iintro %x
  obtain ⟨H, hw, hl⟩ := x
  dsimp only
  by_cases h0 : H.head = 0
  · ------------------------------------------------------------------ empty list
    have hw0 : HeapModel.wf { H with freeList := [] } live 0 := by
      have hg' := hw.geo; have hv' := hw.lives
      exact ⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt, ⟨hg'.bounds, hg'.next_al, hg'.sorted, hg'.next_nb,
        hg'.prev_nb, hg'.first, hg'.disj⟩, AllocFresh.lists_nil rfl, ⟨hv'.live_cell, hv'.cell_live,
        hv'.live_nodup⟩, hw.nf_lo⟩
    iapply (MFunSpec_frame (Fr := frameH n maxP len live)
      (P := fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
        (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp 0 len o1 o2 o4 ∗ vt n 1057464 idx ta (A 578)))))
      (Q := postG n g gt sp size al idx ta (A 578) len maxP iprop(emp) (fun _ _ => iprop(⌜False⌝))) ?hPE ?hQE)
    case hPE =>
      intro args
      iintro HX
      iunfold preX at HX
      icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
      isplitr [Hc]
      · isplitr; · ipureintro; exact ha
        isplitr; · ipureintro; rfl
        iunfold pre581G
        ihave Hh := memBytes_eq (show bytes32 (UInt32.ofNat H.head) = bytes32 0 by rw [h0]; rfl) $$ Hh
        rw [hl]
        iframe Hg Ho1 Ho2 Ho4 Hvt Hh Hl
      · iunfold frameH
        iexists { H with freeList := [] }
        iframe Hlim Hc
        ipureintro; exact ⟨hw0, hl, rfl⟩
    case hQE =>
      intro args rs
      iintro ⟨HF, %p, %hrs, HR⟩
      iexists p
      isplitr; · ipureintro; exact hrs
      iapply finishS (frameH n maxP len live) iprop(emp) (fun _ _ => iprop(⌜False⌝)) hal hk hsize hsize2
        hlen1 hlen0 hroom (by iintro ⟨H, -⟩; iexact H)
        (fun p v _ => by iintro ⟨-, -, -, %hf⟩; exact hf.elim) p
      iframe HF HR
    iapply (f310_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al 0 idx k len maxP o1 o2 o4
      (vt n 1057464 idx ta (A 578)) iprop(emp) (fun _ _ => iprop(⌜False⌝)) hsp hal hk hsize hsize2 hlen0 hlen1
      ho1 ho2 ho4 hroom)
    isplitr; · iexact Hm
    isplitr
    · iapply (MFunSpec_frame (Fr := vt n 1057464 idx ta (A 578))
        (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
          .i32 1057464, .i32 1057464]⌝ ∗ n ↦[wms][ (UInt32.ofNat (sp.toNat - 4)).toNat ] bytes32 0))
        (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[wms][ (UInt32.ofNat (sp.toNat - 4)).toNat ] bytes32 0))
        ?hPW ?hQW)
      case hPW => intro args; iintro ⟨%ha, Hs, Hvt⟩; iframe Hs Hvt; ipureintro; exact ha
      case hQW =>
        intro args rs
        iintro ⟨Hvt, %hrs, Hs⟩
        iunfold walkQ
        iexists 0
        isplitr; · ipureintro; exact hrs
        ileft
        iframe Hs Hvt
        ipureintro; rfl
      iapply (MFunSpec_cost (K := fun _ => 21 * cfg.regularOpCost) (fun _ => by omega))
      iapply (f580_empty cfg lim (d + 1 + 1 + 1) types[34]! (by rfl) inst mi n hm.mem Cg (wordsOf size) al
        (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464)
    iframe H236 H581 H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi
  · ------------------------------------------------------------------ one listed cell
    have hfl1 : ∃ a, H.freeList = [a] ∧ a ≠ 0 := by
      have := hw.lists.fl_len
      unfold HeapModel.head at h0
      match hf : H.freeList, this with
      | [], _ => rw [hf] at h0; simp at h0
      | [a], _ => rw [hf] at h0; exact ⟨a, rfl, by simpa using h0⟩
      | _ :: _ :: _, h => simp at h
    obtain ⟨a, hfl, ha0⟩ := hfl1
    obtain ⟨c, hcat, hcf, hnf⟩ := one_cell hw hfl
    obtain ⟨hcc, hca⟩ := (cellAt_iff' (nodup_of_sorted hw.geo.sorted)).mp hcat
    subst hca
    obtain ⟨s, t, hc⟩ := List.append_of_mem hcc
    obtain ⟨dn, hdn⟩ : ∃ dn : CellM, c.last = false → dn ∈ t ∧ dn.addr = c.next ∧ dn.prev = c.addr := by
      cases hlc : c.last
      · obtain ⟨dn, h1, h2, h3⟩ := nbr_t hw.geo hc hlc
        exact ⟨dn, fun _ => ⟨h1, h2, h3⟩⟩
      · exact ⟨c, fun h => by cases h⟩
    have hb := hw.geo.bounds c hcc
    have hnx := hw.geo.next_al c hcc
    have hlt := hw.len_lt
    have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
    have hnN : (UInt32.ofNat c.next).toNat = c.next := by simp only [UInt32.toNat_ofNat']; omega
    have hlen' : len + 65536 ≤ 2 ^ 32 := by omega
    -- the cell's data out
    iapply (MFunSpec_frame (Fr := iprop(emp))
      (P := fun args => iprop(∃ y : {bs : List UInt8 // bs.length + 4 = c.size},
        (⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            (pre581G n g gt sp (UInt32.ofNat c.addr) len o1 o2 o4 ∗ pwO n c y.1 idx ta (A 578)))) ∗
        frO n maxP live s t c dn))
      (Q := postS n g gt sp size al idx ta (A 578) maxP len live) ?hPO ?hQO)
    case hPO =>
      intro args
      iintro HX
      iunfold preX at HX
      icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
      ihave Hc := (show ([∗list] x ∈ H.cells, cellRes (GF := GF) n live x) ⊢
        [∗list] x ∈ s ++ c :: t, cellRes n live x by rw [hc]) $$ Hc
      icases BigSepL.bigSepL_append.1 $$ Hc with ⟨Hs, Hct⟩
      icases BigSepL.bigSepL_cons.1 $$ Hct with ⟨Hc0, Ht⟩
      icases (cellRes_free n hcf).1 $$ Hc0 with ⟨H0, H4, %bs, %hbs, H8, Hd⟩
      icases next_open hw hc hdn n live (by omega) $$ Ht with ⟨Hn, Hk⟩
      isplitl
      · iexists ⟨bs, hbs⟩
        isplitr [Hs H4 Hk]
        · isplitr; · ipureintro; exact ha
          isplitr; · ipureintro; rfl
          isplitr [H0 H8 Hd Hn Hvt]
          · iunfold pre581G
            ihave Hh := memBytes_eq (show bytes32 (UInt32.ofNat H.head) = bytes32 (UInt32.ofNat c.addr) by
              simp [HeapModel.head, hfl]) $$ Hh
            rw [hl]
            iframe Hg Ho1 Ho2 Ho4 Hh Hl
          · iunfold pwO
            ihave H0 := memBytes_at (b := (UInt32.ofNat c.addr).toNat)
              (bs' := bytes32 (w0 (UInt32.ofNat c.next) c.last)) hcN.symm
              (by rw [AllocSeq.word0_free c hcf hnx (by omega)]) $$ H0
            ihave H8 := memBytes_at (b := (UInt32.ofNat c.addr).toNat + 8) (bs' := bytes32 0)
              (by omega) (by rw [hnf]; rfl) $$ H8
            ihave Hd := memBytes_addr (show c.addr + 12 = (UInt32.ofNat c.addr).toNat + 12 by omega) $$ Hd
            iframe H0 H8 Hd Hn Hvt
        · iunfold frO
          iframe Hlim Hs H4 Hk
      · iempintro
    case hQO => intro args rs; iintro ⟨-, H⟩; iexact H
    iapply MFunSpec_exists
    imodintro
    iintro %y
    obtain ⟨bs, hbs⟩ := y
    dsimp only
    iapply (MFunSpec_frame (Fr := frO n maxP live s t c dn)
      (P := fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗
          (⌜[Value.i32 1074896, .i32 size, .i32 al] = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
            (pre581G n g gt sp (UInt32.ofNat c.addr) len o1 o2 o4 ∗ pwO n c bs idx ta (A 578)))))
      (Q := postG n g gt sp size al idx ta (A 578) len maxP (zO n c bs) (AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578))) ?hPF ?hQF)
    case hPF => intro args; exact .rfl
    case hQF =>
      intro args rs
      iintro ⟨HF, %p, %hrs, HR⟩
      iexists p
      isplitr; · ipureintro; exact hrs
      iapply finishS (frO n maxP live s t c dn) (zO n c bs) (AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578))
        hal hk hsize hsize2 hlen1 hlen0 hroom (restoreO hw hl hc hdn hcf hnf bs hbs)
        (fun p v hp => packOK hw hl hc hdn hfl hcf hnf (by omega) size al k hal hsize hsize2 bs hbs idx ta
          (A 578) _ _ p v hp) p
      iframe HF HR
    iapply (f310_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al (UInt32.ofNat c.addr) idx k
      len maxP o1 o2 o4 (pwO n c bs idx ta (A 578)) (zO n c bs) (AllocSeq.wO n (wordsOf size) al c bs idx ta (A 578))
      hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom)
    isplitr; · iexact Hm
    isplitr
    · iapply (MFunSpec_frame (Fr := iprop(emp))
        (P := fun args => iprop(⌜args = [.i32 (wordsOf size), .i32 al, .i32 (UInt32.ofNat (sp.toNat - 4)),
          .i32 1057464, .i32 1057464]⌝ ∗ oneRes n (UInt32.ofNat (sp.toNat - 4)) (UInt32.ofNat c.addr)
            (UInt32.ofNat c.addr) (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last bs 1057464 idx ta (A 578)))
        ?hPW ?hQW)
      case hPW =>
        intro args
        iintro ⟨%ha, Hs, Hpw⟩
        iunfold pwO at Hpw
        icases Hpw with ⟨H0, H8, Hd, Hn, Hvt⟩
        isplitl [Hs H0 H8 Hd Hn Hvt]
        · isplitr; · ipureintro; exact ha
          iunfold oneRes
          iframe Hs H0 H8 Hd Hn Hvt
        · iempintro
      case hQW =>
        intro args rs
        exact AllocSeq.walkO n (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) c bs idx ta (A 578) args rs (by omega)
      iapply (f580_one cfg lim (d + 1 + 1 + 1) types[34]! (by rfl) inst mi n hm.mem (A 572) (A 576) (A 574) (A 578) ta
        (hm.funcs 572 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 574 (by decide)) hm.table
        types[32]! types[32]! types[0]! (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
        (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464 idx (UInt32.ofNat c.addr)
        (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last bs k hal (by omega)
        (by rw [hW]; omega) (by rw [hW]; omega) (by rw [hcN]; omega) (and3_of_mod4 _ (by rw [hcN]; omega))
        (and3_of_mod4 _ (by rw [hnN]; exact hnx)) (by rw [hcN, hnN]; omega) (by rw [hnN]; omega)
        (by rw [hcN, hnN]; simp only [CellM.size] at hbs; omega))
      rw [hm.types]
      iframe H572 H576 H574 H578 Hi
    iframe H236 H581 H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi

/-- `__rust_alloc` with room: under the limit (`E / 65536 ≤ maxP`) and `align ≤ 8`, the
result is a block. -/
theorem f310_spec_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    n ↪[wmlimit] some maxP ∗
      A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)))
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) 1 ∗ block n p.toNat size.toNat)) := by
  have hk : k < 20 := by
    by_contra hc
    have : 2 ^ 20 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hok := growOk_of_room len _ maxP hlen0 hroom hmax
  refine (f310_spec_seq cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k maxP len live
    o1 o2 o4 hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom).trans
    (MFunSpec_frame iprop(emp) ?hP ?hQ)
  case hP => intro args; iintro H; isplitl [H]; · iexact H
             · iempintro
  case hQ =>
    intro args rs
    iintro ⟨-, %p, %hrs, Hg, Hst, Hvt, HO⟩
    iunfold allocOutS at HO
    icases HO with (⟨%⟨hp, hpa⟩, %len', %hl', Hinv, Hb⟩ | ⟨%⟨-, hbad⟩, -⟩)
    · iexists p
      isplitr; · ipureintro; exact ⟨hrs, hp, hpa⟩
      iframe Hg Hst Hvt
      iexists len'
      iframe Hinv Hb
      ipureintro; exact hl'
    · exfalso
      rcases hbad with h | h
      · exact h hok
      · omega

end Spec

end WNear.Binary.AllocSeq
