import Bridge.Functions.AllocTwoModel
import Bridge.Functions.AllocTwoF580

/-!
# Packing the two-cell walks into `heapInv` (M4)

The resource side of an allocation from `heapInv … 2` with a free list `[a, b]`:

* `open_skip`: `a` too small: `b` opened as `AllocSeq` opens a one-cell list (its walk resources
  and `frO` on the model `skipM` where only `b` is listed), and `a`'s word 0 and `next_free`
  (`aPart`, all the skip reads) out of `frO`, given back unchanged;
* `open_merge`: `a` with `CAN_MERGE`: the cells `s ++ b :: a :: t`, `a` and `b`'s walk resources
  (`AllocTwoWalk.mergeRes`) and the rest, which is `frO` of the merged model `mergedM` around
  the grown `b`;
* `open_first`: `a` fits: `a` opened as a one-cell list (`b` stays in `frO`).
-/

namespace WNear.Binary.AllocTwo

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeqModel WNear.Binary.AllocSeq
open WNear.Binary.AllocFirstFit (nextW nextW_true nextW_false w0)
open WNear.Binary.AllocDealloc (upd mem_map_upd nodup_of_sorted cellAt_iff' mem_unique cellRes_free
  cellRes_split cellData memBytes_at bigSep_extract bigSep_upd nodup_sublist_erase mem_erase_iff')
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq)

section Open

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What skipping a cell reads: its word 0 and `next_free`. -/
def aPart (n : Nat) (x : CellM) : IProp GF :=
  iprop(n ↦[i32][ x.addr ] UInt32.ofNat x.word0 ∗ n ↦[i32][ x.addr + 8 ] UInt32.ofNat x.nextFree)

/-- A free cell's `aPart` out of a list of cells, to be given back. -/
theorem part_extract (n : Nat) (live : List (Nat × Nat)) {L : List CellM} {x : CellM} (hx : x ∈ L)
    (hxf : x.allocated = false) :
    ([∗list] y ∈ L, cellRes (GF := GF) n live y) ⊢ aPart n x ∗ (aPart n x -∗ [∗list] y ∈ L, cellRes n live y) := by
  iintro H
  icases (bigSep_extract hx).1 $$ H with ⟨Hx, Hr⟩
  icases (cellRes_free n hxf).1 $$ Hx with ⟨H0, H4, %bs, %hbs, H8, Hd⟩
  iunfold aPart
  iframe H0 H8
  iintro ⟨H0, H8⟩
  iapply (bigSep_extract hx).2
  iframe Hr
  iapply (cellRes_free n hxf).2
  iframe H0 H4
  iexists bs
  iframe H8 Hd
  ipureintro; exact hbs

theorem cellData_lit (n : Nat) (live : List (Nat × Nat)) (x : CellM) (v : Nat) :
    cellData (GF := GF) n live ⟨x.addr, x.next, v, x.last, x.allocated, x.nextFree⟩ = cellData n live x := rfl

/-- `x`'s `aPart` and the `prev` word of another cell `d`, out of a list of cells; given back with
`d`'s `prev` set to any `v`. -/
theorem part_nbr (n : Nat) (live : List (Nat × Nat)) {L : List CellM} {x d : CellM}
    (hnd : (L.map CellM.addr).Nodup) (hx : x ∈ L) (hxf : x.allocated = false) (hd : d ∈ L) :
    ([∗list] y ∈ L, cellRes (GF := GF) n live y) ⊢ aPart n x ∗ n ↦[i32][ d.addr + 4 ] UInt32.ofNat d.prev ∗
      (aPart n x -∗ ∀ v : Nat, n ↦[i32][ d.addr + 4 ] UInt32.ofNat v -∗
        [∗list] y ∈ L.map (upd d.addr { d with prev := v }), cellRes n live y) := by
  iintro H
  icases (bigSep_extract hd).1 $$ H with ⟨Hd, Hr⟩
  by_cases hxd : x = d
  · subst hxd
    icases (cellRes_free n hxf).1 $$ Hd with ⟨D0, D1, %bs, %hbs, D8, Dd⟩
    iunfold aPart
    iframe D0 D8 D1
    iintro ⟨D0, D8⟩ %v D1
    iapply (bigSep_upd (Φ := cellRes n live) (y := { x with prev := v }) hnd hx rfl rfl).2
    iframe Hr
    iapply (cellRes_free n (x := { x with prev := v }) hxf).2
    simp only [CellM.word0]
    iframe D0 D1
    iexists bs
    iframe D8 Dd
    ipureintro; exact hbs
  · icases (cellRes_split n live d).1 $$ Hd with ⟨D0, D1, DD⟩
    have hxE : x ∈ L.erase d := (mem_erase_iff' hnd hd).mpr ⟨hx, fun e => hxd (mem_unique hnd hx hd e)⟩
    icases part_extract n live hxE hxf $$ Hr with ⟨HA, HK⟩
    iframe HA D1
    iintro HA %v D1
    iapply (bigSep_upd (Φ := cellRes n live) (y := { d with prev := v }) hnd hd rfl rfl).2
    isplitl [D0 D1 DD]
    · iapply (cellRes_split n live _).2
      rw [show cellData (GF := GF) n live { d with prev := v } = cellData n live d from rfl]
      iframe DD
      isplitl [D0]
      · iapply (memBytes_at (a := d.addr) (b := ({ d with prev := v } : CellM).addr)
          (bs := bytes32 (UInt32.ofNat d.word0)) (bs' := bytes32 (UInt32.ofNat ({ d with prev := v } : CellM).word0))
          rfl rfl) $$ D0
      iapply (memBytes_at (a := d.addr + 4) (b := ({ d with prev := v } : CellM).addr + 4)
        (bs := bytes32 (UInt32.ofNat v)) (bs' := bytes32 (UInt32.ofNat ({ d with prev := v } : CellM).prev))
        rfl rfl) $$ D1
    iapply HK $$ HA

variable {n maxP : Nat} {live : List (Nat × Nat)} {H : HeapModel} {F : Nat} {s t : List CellM}
  {c d : CellM} (hw : H.wf live F) (hc : H.cells = s ++ c :: t)
  (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr)
include hw hc hd


/-- The next neighbour's `prev` word, out of the cells after `c`. -/
theorem next_open2 (n : Nat) (live' : List (Nat × Nat)) (hcn : c.next < 2 ^ 32) :
    ([∗list] x ∈ t, cellRes (GF := GF) n live' x) ⊢
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗
      (∀ v : Nat, nextW n (UInt32.ofNat c.next) (UInt32.ofNat v) c.last -∗
        [∗list] x ∈ tS c v d t, cellRes n live' x) := by
  cases hlc : c.last
  · obtain ⟨hdt, hda, hdp⟩ := hd hlc
    have hnd : (t.map CellM.addr).Nodup := nodup_of_sorted (sorted_parts hw.geo hc).2.1
    rw [nextW_false]
    iintro Ht
    icases (bigSep_extract hdt).1 $$ Ht with ⟨Hd, Ht⟩
    icases (cellRes_split n live' d).1 $$ Hd with ⟨H0, H1, HD⟩
    isplitl [H1]
    · iapply memBytes_at (by simp only [UInt32.toNat_ofNat']; omega) (by rw [hdp]) $$ H1
    iintro %v Hv
    rw [nextW_false]
    unfold tS; rw [hlc]; simp only [Bool.false_eq_true, ↓reduceIte]
    iapply (bigSep_upd (Φ := cellRes n live') (y := { d with prev := v }) hnd hdt rfl rfl).2
    iframe Ht
    iapply (cellRes_split n live' _).2
    rw [show cellData (GF := GF) n live' { d with prev := v } = cellData n live' d from rfl]
    iframe HD
    isplitl [H0]
    · iapply (memBytes_at (a := d.addr) (b := ({ d with prev := v } : CellM).addr)
        (bs := bytes32 (UInt32.ofNat d.word0))
        (bs' := bytes32 (UInt32.ofNat ({ d with prev := v } : CellM).word0)) rfl rfl) $$ H0
    iapply (memBytes_at (b := ({ d with prev := v } : CellM).addr + 4)
      (bs' := bytes32 (UInt32.ofNat ({ d with prev := v } : CellM).prev))
      (by simp only [UInt32.toNat_ofNat']; omega) rfl) $$ Hv
  · rw [nextW_true]
    iintro Ht
    isplitr; · iempintro
    iintro %v -
    unfold tS; rw [hlc]; simp only [↓reduceIte]
    iexact Ht

/-- The one-cell opening of `c` (as in `AllocSeq.f310_spec_seq`), with another free cell `x`'s
`aPart` out of the frame. -/
theorem open_skip (hcf : c.allocated = false) {x : CellM} (hx : x ∈ H.cells) (hxf : x.allocated = false)
    (hxc : x ≠ c) :
    n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      n ↦[i32][ c.addr ] UInt32.ofNat c.word0 ∗ n ↦[i32][ c.addr + 8 ] UInt32.ofNat c.nextFree ∗
      (∃ bs : List UInt8, ⌜bs.length + 4 = c.size⌝ ∗ n ↦[wms][ c.addr + 12 ] bs) ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗ aPart n x ∗
      (aPart n x -∗ frO n maxP live s t c d) := by
  have hnd := nodup_of_sorted hw.geo.sorted
  have hcn := hw.geo.bounds c ((mem_cells hc c).mpr (Or.inr (Or.inl rfl)))
  have hlt := hw.len_lt
  have hndt : (t.map CellM.addr).Nodup := nodup_of_sorted (sorted_parts hw.geo hc).2.1
  iintro ⟨#Hm, Hc⟩
  ihave Hc := (show ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
    [∗list] y ∈ s ++ c :: t, cellRes n live y by rw [hc]) $$ Hc
  icases BigSepL.bigSepL_append.1 $$ Hc with ⟨Hs, Hct⟩
  icases BigSepL.bigSepL_cons.1 $$ Hct with ⟨Hc0, Ht⟩
  icases (cellRes_free n hcf).1 $$ Hc0 with ⟨H0, H4, %bs, %hbs, H8, Hd⟩
  iframe H0 H8
  isplitl [Hd]
  · iexists bs; iframe Hd; ipureintro; exact hbs
  rcases (mem_cells hc x).mp hx with hxs | rfl | hxt
  · -- `x` before `c`
    icases next_open2 hw hc hd n live (by omega) $$ Ht with ⟨Hn, Hk⟩
    icases part_extract n live hxs hxf $$ Hs with ⟨HA, HK⟩
    iframe Hn HA
    iintro HA
    iunfold frO
    iframe Hm H4 Hk
    iapply HK $$ HA
  · exact absurd rfl hxc
  · cases hlc : c.last
    · obtain ⟨hdt, hda, hdp⟩ := hd hlc
      icases part_nbr n live hndt hxt hxf hdt $$ Ht with ⟨HA, H1, HK⟩
      rw [nextW_false]
      isplitl [H1]
      · iapply memBytes_at (by simp only [UInt32.toNat_ofNat']; omega) (by rw [hdp]) $$ H1
      iframe HA
      iintro HA
      iunfold frO
      iframe Hm Hs H4
      iintro %v Hv
      rw [hlc, nextW_false]
      unfold tS; rw [hlc]; simp only [Bool.false_eq_true, ↓reduceIte]
      iapply HK $$ HA %v
      iapply memBytes_at (by simp only [UInt32.toNat_ofNat']; omega) rfl $$ Hv
    · rw [nextW_true]
      icases part_extract n live hxt hxf $$ Ht with ⟨HA, HK⟩
      isplitr; · iempintro
      iframe HA
      iintro HA
      iunfold frO
      iframe Hm Hs H4
      iintro %v -
      unfold tS; rw [hlc]; simp only [↓reduceIte]
      iapply HK $$ HA

end Open

section Merge

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocTwoWalk (mergeRes)

variable {n maxP : Nat} {live : List (Nat × Nat)} {H : HeapModel} {F : Nat} {s t : List CellM}
  {cb ca : CellM} (hw : H.wf live F) (hc : H.cells = s ++ cb :: ca :: t)
  (hcbf : cb.allocated = false) (hcaf : ca.allocated = false) (hcbn : cb.next = ca.addr)
  (hcbl : cb.last = false) (hcap : ca.prev = cb.addr) (hcanf : ca.nextFree = cb.addr + 1)
  (hcbnf : cb.nextFree = 0)
include hw hc hcbf hcaf hcbn hcbl hcap hcanf hcbnf

/-- The walk resources of the merge (`a` before the merge, `b` its previous neighbour), common to
both shapes. -/
theorem open_mergeAB :
    ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ bsa bsb : List UInt8, ⌜bsa.length + 12 + ca.addr = ca.next ∧ bsb.length + 12 + cb.addr = ca.addr⌝ ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat ] w0 (UInt32.ofNat ca.next) ca.last ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 4 ] UInt32.ofNat cb.addr ∗
      n ↦[i32][ (UInt32.ofNat ca.addr).toNat + 8 ] (UInt32.ofNat cb.addr ||| 1) ∗
      n ↦[wms][ (UInt32.ofNat ca.addr).toNat + 12 ] bsa ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat ] UInt32.ofNat ca.addr ∗
      n ↦[i32][ (UInt32.ofNat cb.addr).toNat + 8 ] 0 ∗
      n ↦[wms][ (UInt32.ofNat cb.addr).toNat + 12 ] bsb ∗
      ([∗list] y ∈ s, cellRes n live y) ∗ n ↦[i32][ cb.addr + 4 ] UInt32.ofNat cb.prev ∗
      ([∗list] y ∈ t, cellRes n live y) := by
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have ba := hw.geo.bounds ca hca
  have bb := hw.geo.bounds cb hcb
  have hna := hw.geo.next_al ca hca
  have hlt := hw.len_lt
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
  · iapply memBytes_at (by omega) (by rw [hcbnf]; rfl) $$ B8
  iapply memBytes_addr (by omega) $$ Bd

/-- The merge's walk resources and `frO` of the merged model, `a` the last cell of its chunk. -/
theorem open_merge1 (hlast : ca.last = true) (d : CellM) :
    n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ bsa bsb : List UInt8, ⌜bsa.length + 12 + ca.addr = ca.next ∧ bsb.length + 12 + cb.addr = ca.addr⌝ ∗
      mergeRes n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last bsa bsb ∗
      frO n maxP live s t (bM cb ca) d := by
  iintro ⟨#Hm, Hc⟩
  icases open_mergeAB hw hc hcbf hcaf hcbn hcbl hcap hcanf hcbnf $$ Hc with
    ⟨%bsa, %bsb, %hl, A0, A4, A8, Ad, B0, B8, Bd, Hs, B4, Ht⟩
  iexists bsa, bsb
  iframe %hl
  iunfold mergeRes
  rw [hlast, nextW_true]
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

/-- The merge's walk resources and `frO` of the merged model, `a` followed by `m` in its chunk. -/
theorem open_merge2 (hlast : ca.last = false) {m : CellM} {t' : List CellM} (ht : t = m :: t')
    (hmaddr : m.addr = ca.next) (hmprev : m.prev = ca.addr) :
    n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      ∃ bsa bsb : List UInt8, ⌜bsa.length + 12 + ca.addr = ca.next ∧ bsb.length + 12 + cb.addr = ca.addr⌝ ∗
      mergeRes n (UInt32.ofNat ca.addr) (UInt32.ofNat ca.next) (UInt32.ofNat cb.addr) ca.last bsa bsb ∗
      frO n maxP live s ({ m with prev := cb.addr } :: t') (bM cb ca) { m with prev := cb.addr } := by
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have ba := hw.geo.bounds ca hca
  have hlt := hw.len_lt
  have hT' : ∀ x ∈ t', x.addr ≠ m.addr := by
    intro x hx
    have hs := hw.geo.sorted
    rw [hc, ht, List.map_append, List.map_cons, List.map_cons, List.map_cons, List.pairwise_append,
      List.pairwise_cons, List.pairwise_cons, List.pairwise_cons] at hs
    have := hs.2.1.2.2.1 _ (List.mem_map_of_mem hx); omega
  iintro ⟨#Hm, Hc⟩
  icases open_mergeAB hw hc hcbf hcaf hcbn hcbl hcap hcanf hcbnf $$ Hc with
    ⟨%bsa, %bsb, %hl, A0, A4, A8, Ad, B0, B8, Bd, Hs, B4, Ht⟩
  rw [ht]
  icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Hmr, Ht⟩
  icases (cellRes_split n live m).1 $$ Hmr with ⟨M0, M1, MD⟩
  iexists bsa, bsb
  iframe %hl
  iunfold mergeRes
  rw [hlast, nextW_false]
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

end Merge

section First

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocFirstFit (aN aN_mod4 v_false and3_of_mod4)
open WNear.Binary.AllocFresh (heapInv_intro bigSep_cons sub8_ofNat)
open WNear.Binary.AllocDealloc (cellRes_free_intro cellRes_alloc)
open WNear.Binary.U128From (memBytes_split memBytes_join)

variable {n maxP len : Nat} {live : List (Nat × Nat)} {H : HeapModel} {F : Nat} {s t : List CellM} {c d : CellM}
  (hw : H.wf live F) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
  (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr) (hcf : c.allocated = false)

include hw hc hd hcf in
/-- The one-cell opening of `c` (as in `AllocSeq.f310_spec_seq`), for any bound on the list. -/
theorem open_one :
    n ↪[wmlimit] some maxP ∗ ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
      n ↦[i32][ c.addr ] UInt32.ofNat c.word0 ∗ n ↦[i32][ c.addr + 8 ] UInt32.ofNat c.nextFree ∗
      (∃ bs : List UInt8, ⌜bs.length + 4 = c.size⌝ ∗ n ↦[wms][ c.addr + 12 ] bs) ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last ∗ frO n maxP live s t c d := by
  have hcn := hw.geo.bounds c ((mem_cells hc c).mpr (Or.inr (Or.inl rfl)))
  have hlt := hw.len_lt
  iintro ⟨#Hm, Hc⟩
  ihave Hc := (show ([∗list] y ∈ H.cells, cellRes (GF := GF) n live y) ⊢
    [∗list] y ∈ s ++ c :: t, cellRes n live y by rw [hc]) $$ Hc
  icases BigSepL.bigSepL_append.1 $$ Hc with ⟨Hs, Hct⟩
  icases BigSepL.bigSepL_cons.1 $$ Hct with ⟨Hc0, Ht⟩
  icases (cellRes_free n hcf).1 $$ Hc0 with ⟨H0, H4, %bs, %hbs, H8, Hd⟩
  icases next_open2 hw hc hd n live (by omega) $$ Ht with ⟨Hn, Hk⟩
  iframe H0 H8 Hn
  isplitl [Hd]
  · iexists bs; iframe Hd; ipureintro; exact hbs
  iunfold frO
  iframe Hm Hs H4 Hk

include hw hl hc hd hcf in
/-- 580 took the listed `c` whole (its `next_free` `b`, the next listed cell): allocated in place,
lent as `(c + 8, size)`, the list `[b]`. -/
theorem packWO2 (w al p : UInt32) (hp : p.toNat = c.addr + 8)
    (hfit : 4 * w.toNat ≤ c.next - c.addr - 8) {size : Nat} (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (bs : List UInt8) (hbs : bs.length + 4 = c.size) {b : Nat} {cb : CellM} (hcb : H.cellAt b = some cb)
    (hcbf : cb.allocated = false) (hnfb : cb.nextFree = 0) (hbc : b ≠ c.addr) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[wmlength] len ∗ n ↦[i32][ (1074896 : UInt32).toNat ] UInt32.ofNat b ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat b ∗ n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last
      ⊢ heapInv n maxP len ((p.toNat, size) :: live) 1 ∗ block n p.toNat size := by
  have hg := hw.geo
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hg.bounds c hcc
  have hnx := hg.next_al c hcc
  have hlt := hw.len_lt
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hsz : c.size = c.next - c.addr - 8 := rfl
  iintro ⟨Hfr, Hl, Hh, H0, H8, Hd, Hn⟩
  iunfold frO at Hfr
  icases Hfr with ⟨#Hm, Hs, H4, Hk⟩
  ihave Ht := Hk $$ %c.addr Hn
  rw [tS_self2 hw hc hd, hp]
  ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 8 + 4 by omega) $$ Hd
  ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
  ihave Hd := memBytes_join n (c.addr + 8) 4 (bytes32 (UInt32.ofNat b)) bs (by simp [bytes32]) $$ [H8 Hd]
  · iframe H8 Hd
  icases memBytes_split n (c.addr + 8) size (bytes32 (UInt32.ofNat b) ++ bs) (by simp [bytes32]; omega) $$ Hd with ⟨Hb, Hsl⟩
  isplitr [Hb]
  · iapply heapInv_intro (modelW2 H s t c b) (wf_whole2 hw hc hcf hs0 (by omega) hcb hcbf hnfb hbc) hl (UInt32.ofNat b)
      (by simp [HeapModel.head, modelW2])
    ihave Hh := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hh
    iframe Hh Hl Hm
    rw [show (modelW2 H s t c b).cells = s ++ cW c :: t from rfl]
    iapply BigSepL.bigSepL_append.2
    isplitl [Hs]
    · iapply bigSep_cons $$ Hs
    iapply BigSepL.bigSepL_cons.2
    isplitr [Ht]
    · iapply (cellRes_alloc n (x := cW c) rfl).2
      ihave H0 := memBytes_at (b := (cW c).addr) (bs' := bytes32 (UInt32.ofNat (cW c).word0)) hcN
        (by rw [word0_alloc (cW c) rfl (by exact hnx) (by show c.next + 3 < 2 ^ 32; omega)]; rfl) $$ H0
      iframe H0
      isplitl [H4]
      · iapply (memBytes_at (a := c.addr + 4) (b := (cW c).addr + 4) (bs := bytes32 (UInt32.ofNat c.prev)) (bs' := bytes32 (UInt32.ofNat (cW c).prev)) rfl rfl) $$ H4
      iexists size, (bytes32 (UInt32.ofNat b) ++ bs).drop size
      ihave Hsl := memBytes_at (a := c.addr + 8 + size) (b := (cW c).addr + 8 + size) (bs := (bytes32 (UInt32.ofNat b) ++ bs).drop size) (bs' := (bytes32 (UInt32.ofNat b) ++ bs).drop size) rfl rfl $$ Hsl
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
/-- 580 split the listed `c` (its `next_free` `b`, the next listed cell) at `p - 8`: `c` shrunk and
still first in the list `[c, b]`, the new cell lent as `(p, size)`. -/
theorem packSO2 (w al p : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (ha0 : 0 < c.addr)
    (hp : p.toNat = aN (UInt32.ofNat c.next) w al)
    (hfit : 4 * w.toNat ≤ c.next - c.addr - 8) (hcs : c.addr + 80 ≤ p.toNat) (hw1 : 1 ≤ w.toNat)
    {size : Nat} (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (bs : List UInt8) (hbs : bs.length + 4 = c.size) {b : Nat} (hfl : H.freeList = [c.addr, b])
    (hnf : c.nextFree = b) (hnm : ∀ x ∈ t, x.addr ∈ H.freeList → x.nextFree % 2 = 0) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[wmlength] len ∗
      n ↦[i32][ (1074896 : UInt32).toNat ] UInt32.ofNat c.addr ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (p - 8) ∗ n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] UInt32.ofNat b ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs.take (p.toNat - 8 - (UInt32.ofNat c.addr).toNat - 12) ∗
      n ↦[i32][ p.toNat - 8 ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ p.toNat - 4 ] UInt32.ofNat c.addr ∗
      (∃ bs' : List UInt8, ⌜bs'.length = (UInt32.ofNat c.next).toNat - p.toNat⌝ ∗ n ↦[wms][ p.toNat ] bs') ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr &&& 3 ||| (p - 8)) c.last
      ⊢ heapInv n maxP len ((p.toNat, size) :: live) F ∗ block n p.toNat size := by
  have hg := hw.geo
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hg.bounds c hcc
  have hnx := hg.next_al c hcc
  have hlt := hw.len_lt
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  have hnN : (UInt32.ofNat c.next).toNat = c.next := by simp only [UInt32.toNat_ofNat']; omega
  have hsz : c.size = c.next - c.addr - 8 := rfl
  have hA1 : p.toNat + 4 * w.toNat ≤ c.next := by
    have : aN (UInt32.ofNat c.next) w al ≤ c.next - 4 * w.toNat := by unfold aN; rw [hnN]; exact Nat.sub_le _ _
    omega
  have hA4 : p.toNat % 4 = 0 := by rw [hp]; exact aN_mod4 _ w al k hal (by rw [hnN]; exact hnx)
  have hm8 : p - 8 = UInt32.ofNat (p.toNat - 8) := sub8_ofNat p (by omega)
  have hv : UInt32.ofNat c.addr &&& 3 ||| (p - 8) = UInt32.ofNat (p.toNat - 8) := by
    rw [v_false _ _ (and3_of_mod4 _ (by rw [hcN]; omega)), hm8]
  have hwf := wf_split2 hw hc hd hcf hnm ha0 (m := p.toNat - 8) (by omega) (by omega) (by omega)
    hs0 (size := size) (by omega)
  rw [show p.toNat - 8 + 8 = p.toNat by omega] at hwf
  iintro ⟨Hfr, Hl, Hh, H0, H8, Hd, HN0, HN1, HB, Hn⟩
  iunfold frO at Hfr
  icases Hfr with ⟨#Hm, Hs, H4, Hk⟩
  rw [hv]
  ihave Ht := Hk $$ %(p.toNat - 8) Hn
  icases HB with ⟨%bs', %hbs', HB⟩
  icases memBytes_split n p.toNat size bs' (by rw [hbs', hnN]; omega) $$ HB with ⟨Hb, Hsl⟩
  isplitr [Hb]
  · iapply heapInv_intro (modelS H s t c (p.toNat - 8) d) hwf hl (UInt32.ofNat c.addr)
      (by simp [HeapModel.head, modelS, hfl])
    ihave Hh := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hh
    iframe Hh Hl Hm
    rw [show (modelS H s t c (p.toNat - 8) d).cells =
      s ++ cS c (p.toNat - 8) :: nS c (p.toNat - 8) :: tS c (p.toNat - 8) d t from rfl]
    iapply BigSepL.bigSepL_append.2
    isplitl [Hs]
    · iapply bigSep_cons $$ Hs
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0 H4 H8 Hd]
    · ihave H0 := memBytes_at (b := c.addr) (bs' := bytes32 (UInt32.ofNat (p.toNat - 8))) hcN
        (by rw [hm8]) $$ H0
      ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
      ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 12 by omega) $$ Hd
      iapply cellRes_free_intro (cS c (p.toNat - 8)) hcf (a := c.addr) (w0 := UInt32.ofNat (p.toNat - 8)) (w1 := UInt32.ofNat c.prev) (nf := UInt32.ofNat b) rfl (by simp [cS, CellM.word0, hcf]) rfl
        (by simp [cS, hnf]) (bs.take (p.toNat - 8 - (UInt32.ofNat c.addr).toNat - 12)) (by simp [cS, CellM.size, hcN]; omega)
      iframe H0 H4 H8 Hd
    iapply BigSepL.bigSepL_cons.2
    isplitl [HN0 HN1 Hsl]
    · iapply (cellRes_alloc n (x := nS c (p.toNat - 8)) rfl).2
      ihave HN0 := memBytes_at (a := p.toNat - 8) (bs := bytes32 (w0 (UInt32.ofNat c.next) c.last ||| 1)) (b := (nS c (p.toNat - 8)).addr)
        (bs' := bytes32 (UInt32.ofNat (nS c (p.toNat - 8)).word0)) rfl
        (by rw [word0_alloc (nS c (p.toNat - 8)) rfl (by exact hnx) (by show c.next + 3 < 2 ^ 32; omega)]; rfl) $$ HN0
      ihave HN1 := memBytes_at (a := p.toNat - 4) (bs := bytes32 (UInt32.ofNat c.addr)) (b := (nS c (p.toNat - 8)).addr + 4)
        (bs' := bytes32 (UInt32.ofNat (nS c (p.toNat - 8)).prev)) (by simp [nS]; omega) rfl $$ HN1
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


end First

end WNear.Binary.AllocTwo
