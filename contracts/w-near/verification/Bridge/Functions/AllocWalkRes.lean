import Bridge.Functions.AllocTwoPack
import Bridge.Functions.AllocWalkModel

/-!
# The resources of one step of 580's walk over any free list (M4)

The walk's loop invariant holds the heap's cells as `[∗list] c ∈ H.cells, cellRes n live c` for a
model `H` (`AllocWalkModel`). Each step opens the cells it touches and closes them back on the
next model:

* `open_oneW` / `close_oneW`: the listed head `c` (free) as `AllocTwoWalk.body7` reads it (word 0,
  `next_free`, data, the next neighbour's `prev` word), the rest kept aside as `AllocSeq.frO`;
  closing gives back the same cells (the head unlinked, or untouched);
* `packWG` / `packSG`: the head taken whole or split, packed as `heapW` (the heap with the new
  block lent, and the block);
* `openMG` / `closeMG`: the head `a` with `CAN_MERGE` and its previous neighbour `b` as
  `AllocTwoWalk.merge7` reads them, and, after the merge, the cells of `mergedG` (`b` grown to
  `a`'s end). `openMG` is `AllocTwo.open_mergeAB`/`open_merge1`/`open_merge2` with `b`'s
  `next_free` any value (there it is 0).
-/

namespace WNear.Binary.AllocWalk

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeqModel WNear.Binary.AllocSeq WNear.Binary.AllocTwo
open WNear.Binary.AllocFirstFit (nextW nextW_true nextW_false w0 aN aN_mod4 v_false and3_of_mod4)
open WNear.Binary.AllocDealloc (upd mem_map_upd nodup_of_sorted cellAt_iff' mem_unique cellRes_free
  cellRes_split cellData memBytes_at cellRes_free_intro cellRes_alloc)
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq)
open WNear.Binary.AllocFresh (bigSep_cons sub8_ofNat)
open WNear.Binary.U128From (memBytes_split memBytes_join)

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The heap after the walk lent `(p, size)`: a model with the block lent, its head `v`, and the
block. -/
def heapW (n : Nat) (live : List (Nat × Nat)) (F len p size : Nat) (v : UInt32) : IProp GF :=
  iprop(∃ H : HeapModel, ⌜H.wf ((p, size) :: live) F ∧ H.len = len ∧ v = UInt32.ofNat H.head⌝ ∗
    ([∗list] c ∈ H.cells, cellRes n ((p, size) :: live) c) ∗ block n p size)

/-- A neighbour for `open_oneW` (any cell if `c` is last). -/
theorem nbr_any {H : HeapModel} (hg : Geo H) {s t : List CellM} {c : CellM} (hc : H.cells = s ++ c :: t) :
    ∃ d, c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr := by
  cases hl : c.last
  · obtain ⟨d, h⟩ := nbr_t hg hc hl
    exact ⟨d, fun _ => h⟩
  · exact ⟨c, fun h => by cases h⟩

section One

variable {n maxP len : Nat} {live : List (Nat × Nat)} {H : HeapModel} {F : Nat} {s t : List CellM}
  {c d : CellM} (hw : H.wf live F) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
  (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr) (hcf : c.allocated = false)

include hw hc hd hcf in
/-- The free cell `c` opened as the walk reads it, the rest kept aside as `frO`. -/
theorem open_oneW :
    n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ bs : List UInt8, ⌜bs.length + 12 + c.addr = c.next⌝ ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] w0 (UInt32.ofNat c.next) c.last ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗ frO n maxP live s t c d := by
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hw.geo.bounds c hcc
  have hnx := hw.geo.next_al c hcc
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro Hh
  icases open_one (n := n) (maxP := maxP) hw hc hd hcf $$ Hh with ⟨H0, H8, ⟨%bs, %hbs, Hd⟩, Hn, Hfr⟩
  iexists bs
  isplitr; · ipureintro; unfold CellM.size at hbs; omega
  iframe Hn Hfr
  isplitl [H0]; · iapply memBytes_at hcN.symm (by rw [word0_free c hcf hnx (by omega)]) $$ H0
  isplitl [H8]; · iapply memBytes_addr (by omega) $$ H8
  iapply memBytes_addr (by omega) $$ Hd

include hw hc hd hcf in
/-- `open_oneW` undone: the same cells. -/
theorem close_oneW (bs : List UInt8) (hbs : bs.length + 12 + c.addr = c.next) :
    frO (GF := GF) n maxP live s t c d ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] w0 (UInt32.ofNat c.next) c.last ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ⊢
      [∗list] y ∈ H.cells, cellRes n live y := by
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hw.geo.bounds c hcc
  have hnx := hw.geo.next_al c hcc
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨Hfr, H0, H8, Hd, Hn⟩
  iunfold frO at Hfr
  icases Hfr with ⟨-, Hs, H4, Hk⟩
  ihave Ht := Hk $$ %c.addr Hn
  rw [tS_self2 hw hc hd, hc]
  iapply BigSepL.bigSepL_append.2
  iframe Hs
  iapply BigSepL.bigSepL_cons.2
  iframe Ht
  ihave H0 := memBytes_addr hcN $$ H0
  ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
  ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 12 by omega) $$ Hd
  iapply cellRes_free_intro c hcf rfl (word0_free c hcf hnx (by omega)) rfl rfl bs
    (by unfold CellM.size; omega)
  iframe H0 H4 H8 Hd

include hw hl hc hd hcf in
/-- 580 took the listed head `c` whole: allocated in place, lent as `(c + 8, size)`, the list
its tail. -/
theorem packWG {rest : List Nat} (hfl : H.freeList = c.addr :: rest) (hnf : c.nextFree = rest.headD 0)
    (w p : UInt32) (hp : p.toNat = c.addr + 8)
    (hfit : 4 * w.toNat ≤ c.next - c.addr - 8) {size : Nat} (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (bs : List UInt8) (hbs : bs.length + 12 + c.addr = c.next) :
    frO (GF := GF) n maxP live s t c d ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last
      ⊢ heapW n live F len p.toNat size (UInt32.ofNat c.nextFree) := by
  have hg := hw.geo
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hg.bounds c hcc
  have hnx := hg.next_al c hcc
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨Hfr, H0, H8, Hd, Hn⟩
  iunfold frO at Hfr
  icases Hfr with ⟨-, Hs, H4, Hk⟩
  ihave Ht := Hk $$ %c.addr Hn
  rw [tS_self2 hw hc hd, hp]
  ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 8 + 4 by omega) $$ Hd
  ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
  ihave Hd := memBytes_join n (c.addr + 8) 4 (bytes32 (UInt32.ofNat c.nextFree)) bs (by simp [bytes32]) $$ [H8 Hd]
  · iframe H8 Hd
  icases memBytes_split n (c.addr + 8) size (bytes32 (UInt32.ofNat c.nextFree) ++ bs)
    (by simp [bytes32]; omega) $$ Hd with ⟨Hb, Hsl⟩
  iunfold heapW
  iexists modelWG H s t c rest
  isplitr
  · ipureintro
    exact ⟨wf_wholeG hw hc hcf hfl hs0 (by omega), hl, by simp [HeapModel.head, modelWG, hnf]⟩
  rw [show (modelWG H s t c rest).cells = s ++ cW c :: t from rfl]
  isplitr [Hb]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Hs]
    · iapply bigSep_cons $$ Hs
    iapply BigSepL.bigSepL_cons.2
    isplitr [Ht]
    · iapply (cellRes_alloc n (x := cW c) rfl).2
      ihave H0 := memBytes_at (b := (cW c).addr) (bs' := bytes32 (UInt32.ofNat (cW c).word0)) hcN
        (by rw [word0_alloc (cW c) rfl (by exact hnx) (by show c.next + 3 < 2 ^ 32; omega)]; rfl) $$ H0
      iframe H0
      isplitl [H4]
      · iapply (memBytes_at (a := c.addr + 4) (b := (cW c).addr + 4) (bs := bytes32 (UInt32.ofNat c.prev))
          (bs' := bytes32 (UInt32.ofNat (cW c).prev)) rfl rfl) $$ H4
      iexists size, (bytes32 (UInt32.ofNat c.nextFree) ++ bs).drop size
      ihave Hsl := memBytes_at (a := c.addr + 8 + size) (b := (cW c).addr + 8 + size)
        (bs := (bytes32 (UInt32.ofNat c.nextFree) ++ bs).drop size)
        (bs' := (bytes32 (UInt32.ofNat c.nextFree) ++ bs).drop size) rfl rfl $$ Hsl
      iframe Hsl
      ipureintro
      refine ⟨List.mem_cons_self, ?_⟩
      simp [cW, CellM.size, bytes32]; omega
    iapply bigSep_cons $$ Ht
  · iunfold block
    iexists _
    iframe Hb
    ipureintro; simp; omega

include hw hl hc hd hcf in
/-- 580 split the listed head `c` at `p - 8`: `c` shrunk and still first in the list, the new cell
lent as `(p, size)`. -/
theorem packSG {rest : List Nat} (hfl : H.freeList = c.addr :: rest) (w al p : UInt32) (k : Nat)
    (hal : al.toNat = 2 ^ k) (ha0 : 0 < c.addr)
    (hp : p.toNat = aN (UInt32.ofNat c.next) w al)
    (hfit : 4 * w.toNat ≤ c.next - c.addr - 8) (hcs : c.addr + 80 ≤ p.toNat) (hw1 : 1 ≤ w.toNat)
    {size : Nat} (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (bs : List UInt8) (hbs : bs.length + 12 + c.addr = c.next) :
    frO (GF := GF) n maxP live s t c d ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (p - 8) ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat c.nextFree ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs.take (p.toNat - 8 - (UInt32.ofNat c.addr).toNat - 12) ∗
      n ↦[i32][ p.toNat - 8 ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ p.toNat - 4 ] UInt32.ofNat c.addr ∗
      (∃ bs' : List UInt8, ⌜bs'.length = (UInt32.ofNat c.next).toNat - p.toNat⌝ ∗ n ↦[wms][ p.toNat ] bs') ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr &&& 3 ||| (p - 8)) c.last
      ⊢ heapW n live F len p.toNat size (UInt32.ofNat c.addr) := by
  have hg := hw.geo
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hg.bounds c hcc
  have hnx := hg.next_al c hcc
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnN : (UInt32.ofNat c.next).toNat = c.next := by simp only [UInt32.toNat_ofNat']; omega
  have hA1 : p.toNat + 4 * w.toNat ≤ c.next := by
    have : aN (UInt32.ofNat c.next) w al ≤ c.next - 4 * w.toNat := by unfold aN; rw [hnN]; exact Nat.sub_le _ _
    omega
  have hA4 : p.toNat % 4 = 0 := by rw [hp]; exact aN_mod4 _ w al k hal (by rw [hnN]; exact hnx)
  have hm8 : p - 8 = UInt32.ofNat (p.toNat - 8) := sub8_ofNat p (by omega)
  have hv : UInt32.ofNat c.addr &&& 3 ||| (p - 8) = UInt32.ofNat (p.toNat - 8) := by
    rw [v_false _ _ (and3_of_mod4 _ (by rw [hcN]; omega)), hm8]
  have hwf := wf_splitG hw hc hd hcf hfl ha0 (m := p.toNat - 8) (by omega) (by omega) (by omega)
    hs0 (size := size) (by omega)
  rw [show p.toNat - 8 + 8 = p.toNat by omega] at hwf
  iintro ⟨Hfr, H0, H8, Hd, HN0, HN1, HB, Hn⟩
  iunfold frO at Hfr
  icases Hfr with ⟨-, Hs, H4, Hk⟩
  rw [hv]
  ihave Ht := Hk $$ %(p.toNat - 8) Hn
  icases HB with ⟨%bs', %hbs', HB⟩
  icases memBytes_split n p.toNat size bs' (by rw [hbs', hnN]; omega) $$ HB with ⟨Hb, Hsl⟩
  iunfold heapW
  iexists modelS H s t c (p.toNat - 8) d
  isplitr
  · ipureintro
    exact ⟨hwf, hl, by simp [HeapModel.head, modelS, hfl]⟩
  rw [show (modelS H s t c (p.toNat - 8) d).cells =
    s ++ cS c (p.toNat - 8) :: nS c (p.toNat - 8) :: tS c (p.toNat - 8) d t from rfl]
  isplitr [Hb]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Hs]
    · iapply bigSep_cons $$ Hs
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0 H4 H8 Hd]
    · ihave H0 := memBytes_at (b := c.addr) (bs' := bytes32 (UInt32.ofNat (p.toNat - 8))) hcN
        (by rw [hm8]) $$ H0
      ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
      ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 12 by omega) $$ Hd
      iapply cellRes_free_intro (cS c (p.toNat - 8)) hcf (a := c.addr) (w0 := UInt32.ofNat (p.toNat - 8))
        (w1 := UInt32.ofNat c.prev) (nf := UInt32.ofNat c.nextFree) rfl (by simp [cS, CellM.word0, hcf]) rfl
        (by simp [cS]) (bs.take (p.toNat - 8 - (UInt32.ofNat c.addr).toNat - 12))
        (by simp [cS, CellM.size, hcN]; omega)
      iframe H0 H4 H8 Hd
    iapply BigSepL.bigSepL_cons.2
    isplitl [HN0 HN1 Hsl]
    · iapply (cellRes_alloc n (x := nS c (p.toNat - 8)) rfl).2
      ihave HN0 := memBytes_at (a := p.toNat - 8) (bs := bytes32 (w0 (UInt32.ofNat c.next) c.last ||| 1))
        (b := (nS c (p.toNat - 8)).addr) (bs' := bytes32 (UInt32.ofNat (nS c (p.toNat - 8)).word0)) rfl
        (by rw [word0_alloc (nS c (p.toNat - 8)) rfl (by exact hnx) (by show c.next + 3 < 2 ^ 32; omega)]; rfl) $$ HN0
      ihave HN1 := memBytes_at (a := p.toNat - 4) (bs := bytes32 (UInt32.ofNat c.addr))
        (b := (nS c (p.toNat - 8)).addr + 4) (bs' := bytes32 (UInt32.ofNat (nS c (p.toNat - 8)).prev))
        (by simp [nS]; omega) rfl $$ HN1
      iframe HN0 HN1
      iexists size, bs'.drop size
      ihave Hsl := memBytes_addr (show p.toNat + size = (nS c (p.toNat - 8)).addr + 8 + size by
        simp [nS]; omega) $$ Hsl
      iframe Hsl
      ipureintro
      refine ⟨by simp [nS]; left; omega, ?_⟩
      simp [nS, CellM.size]; omega
    iapply bigSep_cons $$ Ht
  · iunfold block
    iexists _
    iframe Hb
    ipureintro; simp; omega

end One

/-! ## The merge -/

section Merge

variable {n maxP : Nat} {live : List (Nat × Nat)} {H : HeapModel} {F : Nat} {s t : List CellM}
  {cb ca : CellM} (hw : H.wf live F) (hc : H.cells = s ++ cb :: ca :: t)
  (hcbf : cb.allocated = false) (hcaf : ca.allocated = false) (hcbn : cb.next = ca.addr)
  (hcbl : cb.last = false) (hcap : ca.prev = cb.addr) (hcanf : ca.nextFree = cb.addr + 1)
include hw hc hcbf hcaf hcbn hcbl hcap hcanf

/-- `AllocTwo.open_mergeAB` with `b`'s `next_free` any value. -/
theorem open_mergeABG :
    ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ bsa bsb : List UInt8, ⌜bsa.length + 12 + ca.addr = ca.next ∧ bsb.length + 12 + cb.addr = ca.addr⌝ ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 4 ] UInt32.ofNat cb.addr ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] (UInt32.ofNat cb.addr ||| 1) ∗
      n ↦[wms][ (UInt32.ofNat ca.addr).toNat + 12 ] bsa ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat ] UInt32.ofNat ca.addr ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat + 8 ] UInt32.ofNat cb.nextFree ∗
      n ↦[wms][ (UInt32.ofNat cb.addr).toNat + 12 ] bsb ∗
      ([∗list] y ∈ s, cellRes n live y) ∗ n ↦[i32][ cb.addr + 4 ] UInt32.ofNat cb.prev ∗
      ([∗list] y ∈ t, cellRes n live y) := by
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have ba := hw.geo.bounds ca hca
  have bb := hw.geo.bounds cb hcb
  have hna := hw.geo.next_al ca hca
  have hlt := hw.len_lt
  have hla := hw.len_al
  have hcaN : (UInt32.ofNat ca.addr).toNat = ca.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcbN : (UInt32.ofNat cb.addr).toNat = cb.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro Hc
  ihave Hc := (show ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
    [∗list] y ∈ s ++ cb :: ca :: t, cellRes n live y by rw [hc]) $$ Hc
  icases BigSepL.bigSepL_append.1 $$ Hc with ⟨Hs, Hct⟩
  icases BigSepL.bigSepL_cons.1 $$ Hct with ⟨Hb, Hct⟩
  icases BigSepL.bigSepL_cons.1 $$ Hct with ⟨Ha, Ht⟩
  icases (cellRes_free n hcaf).1 $$ Ha with ⟨A0, A4, %bsa, %hbsa, A8, Ad⟩
  icases (cellRes_free n hcbf).1 $$ Hb with ⟨B0, B4, %bsb, %hbsb, B8, Bd⟩
  iexists bsa, bsb
  isplitr
  · ipureintro; unfold CellM.size at hbsa hbsb; omega
  iframe Hs Ht B4
  isplitl [A0]
  · iapply memBytes_at hcaN.symm (by rw [word0_free ca hcaf hna (by omega)]) $$ A0
  isplitl [A4]
  · iapply memBytes_at (by omega) (by rw [hcap]) $$ A4
  isplitl [A8]
  · iapply memBytes_at (by omega) (by rw [hcanf, WNear.Binary.AllocDealloc.or1_ofNat _ bb.2.2.2 (by omega)]) $$ A8
  isplitl [Ad]
  · iapply memBytes_addr (by omega) $$ Ad
  isplitl [B0]
  · iapply memBytes_at hcbN.symm (by rw [word0_free cb hcbf (by rw [hcbn]; omega) (by omega), hcbl, hcbn]; rfl) $$ B0
  isplitl [B8]
  · iapply memBytes_addr (by omega) $$ B8
  iapply memBytes_addr (by omega) $$ Bd

/-- The merge's walk resources and the frame `frO` of the merged cells (`AllocTwo.mergedM`'s, `bM`
the grown `b`, `tm` the cells after it, `dm` its next neighbour). -/
theorem openMG :
    n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ (bsa bsb : List UInt8) (tm : List CellM) (dm : CellM),
      ⌜bsa.length + 12 + ca.addr = ca.next ∧ bsb.length + 12 + cb.addr = ca.addr ∧
        (mergedM H s t cb ca).cells = s ++ bM cb ca :: tm ∧
        ((bM cb ca).last = false → dm ∈ tm ∧ dm.addr = (bM cb ca).next ∧ dm.prev = (bM cb ca).addr)⌝ ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 4 ] UInt32.ofNat cb.addr ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] (UInt32.ofNat cb.addr ||| 1) ∗
      n ↦[wms][ (UInt32.ofNat ca.addr).toNat + 12 ] bsa ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat ] UInt32.ofNat ca.addr ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat + 8 ] UInt32.ofNat cb.nextFree ∗
      n ↦[wms][ (UInt32.ofNat cb.addr).toNat + 12 ] bsb ∗
      nextW n (UInt32.ofNat ca.next) (UInt32.ofNat ca.addr) ca.last ∗
      frO n maxP live s tm (bM cb ca) dm := by
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have ba := hw.geo.bounds ca hca
  have hlt := hw.len_lt
  iintro ⟨#Hm, Hc⟩
  icases open_mergeABG hw hc hcbf hcaf hcbn hcbl hcap hcanf $$ Hc with
    ⟨%bsa, %bsb, %hl, A0, A4, A8, Ad, B0, B8, Bd, Hs, B4, Ht⟩
  cases hlast : ca.last
  · have hc' : H.cells = (s ++ [cb]) ++ ca :: t := by rw [hc]; simp
    obtain ⟨m, t', ht, hmaddr, hmprev⟩ := next_head hw.geo hc' hlast
    subst ht
    have hT' : ∀ x ∈ t', x.addr ≠ m.addr := by
      intro x hx
      have hs := hw.geo.sorted
      rw [hc, List.map_append, List.map_cons, List.map_cons, List.map_cons, List.pairwise_append,
        List.pairwise_cons, List.pairwise_cons, List.pairwise_cons] at hs
      have := hs.2.1.2.2.1 _ (List.mem_map_of_mem hx); omega
    icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Hmr, Ht⟩
    icases (cellRes_split n live m).1 $$ Hmr with ⟨M0, M1, MD⟩
    iexists bsa, bsb, { m with prev := cb.addr } :: t', { m with prev := cb.addr }
    isplitr
    · ipureintro
      refine ⟨hl.1, hl.2, by simp [mergedM, hlast], fun _ => ⟨List.mem_cons_self, by simp [bM, hmaddr], rfl⟩⟩
    rw [nextW_false]
    iframe A0 A4 A8 Ad B0 B8 Bd
    isplitl [M1]
    · iapply memBytes_at (by simp only [UInt32.toNat_ofNat']; omega) (by rw [hmprev]) $$ M1
    iunfold frO
    iframe Hm Hs
    isplitl [B4]
    · iapply (memBytes_at (a := cb.addr + 4) (b := (bM cb ca).addr + 4) (bs := bytes32 (UInt32.ofNat cb.prev))
        (bs' := bytes32 (UInt32.ofNat (bM cb ca).prev)) rfl rfl) $$ B4
    iintro %v Hv
    unfold tS
    rw [show (bM cb ca).last = false by simp [bM, hlast]]
    rw [nextW_false]
    simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons]
    rw [map_upd_out hT']
    iapply BigSepL.bigSepL_cons.2
    iframe Ht
    simp only [upd, ↓reduceIte]
    iapply (cellRes_split n live _).2
    rw [cellData_lit n live m v]
    simp only [CellM.word0]
    iframe MD M0
    iapply (memBytes_at (by simp only [UInt32.toNat_ofNat', bM]; omega) rfl) $$ Hv
  · iexists bsa, bsb, t, ca
    isplitr
    · ipureintro
      refine ⟨hl.1, hl.2, ?_, fun h => by simp [bM, hlast] at h⟩
      cases t with
      | nil => rfl
      | cons m t' => simp [mergedM, hlast]
    rw [nextW_true]
    iframe A0 A4 A8 Ad B0 B8 Bd
    iunfold frO
    iframe Hm Hs
    isplitl [B4]
    · iapply (memBytes_at (a := cb.addr + 4) (b := (bM cb ca).addr + 4) (bs := bytes32 (UInt32.ofNat cb.prev))
        (bs' := bytes32 (UInt32.ofNat (bM cb ca).prev)) rfl rfl) $$ B4
    iintro %v -
    unfold tS
    rw [show (bM cb ca).last = true by simp [bM, hlast]]
    simp only [↓reduceIte]
    iexact Ht

end Merge

section Close

variable {n maxP : Nat} {live : List (Nat × Nat)} {H : HeapModel} {F : Nat} {s t tm : List CellM}
  {cb ca dm : CellM} {rest : List Nat}

/-- After 580's merge (`AllocTwoWalk.merge7`): the cells of the merged model. -/
theorem closeMG (hw : (mergedG H s t cb ca rest).wf live F)
    (hcm : (mergedM H s t cb ca).cells = s ++ bM cb ca :: tm)
    (hdm : (bM cb ca).last = false → dm ∈ tm ∧ dm.addr = (bM cb ca).next ∧ dm.prev = (bM cb ca).addr)
    (hcbf : cb.allocated = false) (bsa bsb : List UInt8)
    (hla : bsa.length + 12 + ca.addr = ca.next) (hlb : bsb.length + 12 + cb.addr = ca.addr)
    (hlt : ca.next < 2 ^ 32) (x y z : UInt32) :
    frO (GF := GF) n maxP live s tm (bM cb ca) dm ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat + 8 ] UInt32.ofNat cb.nextFree ∗
      n ↦[wms][ (UInt32.ofNat cb.addr).toNat + 12 ] bsb ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] x ∗ n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 4 ] y ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] z ∗ n ↦[wms][ (UInt32.ofNat ca.addr).toNat + 12 ] bsa ∗
      nextW n (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last ⊢
      [∗list] y ∈ (mergedG H s t cb ca rest).cells, cellRes n live y := by
  have hcaN : (UInt32.ofNat ca.addr).toNat = ca.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hcbN : (UInt32.ofNat cb.addr).toNat = cb.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hc' : (mergedG H s t cb ca rest).cells = s ++ bM cb ca :: tm := hcm
  iintro ⟨Hfr, B0, B8, Bd, A0, A4, A8, Ad, Hn⟩
  ihave Bd := memBytes_addr (show (UInt32.ofNat cb.addr).toNat + 12 = cb.addr + 12 by omega) $$ Bd
  ihave A0 := memBytes_addr hcaN $$ A0
  ihave A4 := memBytes_addr (show (UInt32.ofNat ca.addr).toNat + 4 = ca.addr + 4 by omega) $$ A4
  ihave A8 := memBytes_addr (show (UInt32.ofNat ca.addr).toNat + 8 = ca.addr + 8 by omega) $$ A8
  ihave Ad := memBytes_addr (show (UInt32.ofNat ca.addr).toNat + 12 = ca.addr + 12 by omega) $$ Ad
  ihave Hd := WNear.Binary.AllocTwoWalk.merge_data n cb.addr ca.addr bsb bsa x y z (by omega) $$ [Bd A0 A4 A8 Ad]
  · iframe Bd A0 A4 A8 Ad
  have key := close_oneW (GF := GF) (n := n) (maxP := maxP) hw hc' hdm hcbf
    (bsb ++ bytes32 x ++ bytes32 y ++ bytes32 z ++ bsa) (by simp [bytes32, bM]; omega)
  rw [show (bM cb ca).addr = cb.addr from rfl, show (bM cb ca).next = ca.next from rfl,
    show (bM cb ca).last = ca.last from rfl, show (bM cb ca).nextFree = cb.nextFree from rfl] at key
  iapply key
  ihave Hd := memBytes_addr (show cb.addr + 12 = (UInt32.ofNat cb.addr).toNat + 12 by omega) $$ Hd
  iframe Hfr B0 B8 Hd Hn

end Close

end Res

end WNear.Binary.AllocWalk
