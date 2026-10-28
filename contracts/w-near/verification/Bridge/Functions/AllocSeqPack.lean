import Bridge.Functions.AllocGen
import Bridge.Functions.AllocSeqModel

/-!
# Packing `__rust_alloc`'s results into `heapInv … 1` (M4)

The resource side of `AllocSeq`: what `AllocGen.res581G` leaves, packed into
`AllocInv.heapInv n maxP len' live' 1`, with the result aligned (`allocOutS`).

* `pack_grownS`: the grown branch (as `AllocFresh.pack_grown`), with `p % align = 0` and,
  when the fresh cell is not used (`p = 0`), `8 < align` (it fits by construction, so it
  was unlinked only for misalignment: AllocFirstFit's finding 5);
* `finishS`: `res581G` for any first walk whose leftovers `Fr ∗ Z` give back
  `AllocFresh.frameH` (the heap with an empty free list) and whose success `W` packs;
* the one-cell free list (`frO`, `zO`, `wO`): `next_open` (the next neighbour's `prev`
  word, out of the cells after `c`), `restoreO` (the walk unlinked `c`: it is leaked),
  `packWO` (whole) and `packSO` (split), `walkO` (580's `post1` as `walkQ`).
-/

namespace WNear.Binary.AllocSeq

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeqModel
open WNear.Binary.AllocFirstFit (post1 vt w0 aN fits canSplit aligned szN aN_mod4 nextW nextW_true
  nextW_false v_false and3_of_mod4)
open WNear.Binary.AllocDealloc (or2_ofNat or1_ofNat cellRes_free_intro cellRes_alloc cellRes_free
  cellRes_split cellData memBytes_at bigSep_extract bigSep_upd nodup_of_sorted mem_unique)
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq cellPages cellPages_toNat cellBytes_toNat
  shl16_toNat cellPages_bounds)
open WNear.Binary.U128From (memBytes_split memBytes_join)
open WNear.Binary.AllocFresh (frameH heapInv_intro pack_fail pack_U pack_W pack_S bigSep_cons w0_last
  w0_last_alloc sub8_ofNat)
open WNear.Binary.AllocAlloc (wordsOf chunkEnd)
open WNear.Binary.AllocGen (walkQ res581G)

/-! ## Arithmetic -/

theorem word0_free (x : CellM) (hx : x.allocated = false) (h4 : x.next % 4 = 0) (h : x.next + 3 < 2 ^ 32) :
    UInt32.ofNat x.word0 = w0 (UInt32.ofNat x.next) x.last := by
  cases hl : x.last
  · simp [CellM.word0, w0, hx, hl]
  · rw [w0_last _ h4 h]; simp [CellM.word0, hx, hl]

theorem word0_alloc (x : CellM) (hx : x.allocated = true) (h4 : x.next % 4 = 0) (h : x.next + 3 < 2 ^ 32) :
    UInt32.ofNat x.word0 = w0 (UInt32.ofNat x.next) x.last ||| 1 := by
  cases hl : x.last
  · rw [show w0 (UInt32.ofNat x.next) false = UInt32.ofNat x.next from rfl, or1_ofNat _ h4 h]
    simp [CellM.word0, hx, hl]
  · rw [w0_last_alloc _ h4 h, show x.word0 = x.next + 3 by simp [CellM.word0, hx, hl]]

theorem al_small (al : UInt32) (k len : Nat) (hal : al.toNat = 2 ^ k) (h8 : al.toNat ≤ 8)
    (hl : len % 65536 = 0) : (len + 8) % al.toNat = 0 := by
  have hk : k ≤ 3 := by
    by_contra hc
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rw [hal]
  interval_cases k <;> simp <;> omega

theorem aN_al (nx w al : UInt32) : aN nx w al % al.toNat = 0 := by
  unfold aN; exact Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

theorem fresh_fits (w al : UInt32) (hw : w.toNat < 2 ^ 29) (hal : al.toNat < 2 ^ 20) :
    4 * w.toNat + 8 ≤ (cellPages w al).toNat * 65536 := by
  rw [cellPages_toNat _ _ hw hal, cellBytes_toNat _ _ hw hal]
  have h1 := le_max_left (w.toNat * 4) ((al.toNat + 64) * 8)
  generalize max (w.toNat * 4) ((al.toNat + 64) * 8) = B at *
  omega

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The outcome of an allocation of `size` bytes from a heap of length `len` (and `E` once
grown by `P` pages): a block `p ≠ 0` aligned to `al`, the heap valid with the free list at
most one cell; or `0` because the limit forbade the grow, or (memory grown) the fresh cell
was misaligned for `al > 8`. -/
def allocOutS (n maxP len E : Nat) (live : List (Nat × Nat)) (size : Nat) (al p : UInt32) (P : Nat) :
    IProp GF :=
  iprop((⌜p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗ ∃ len', ⌜len' = len ∨ len' = E⌝ ∗
      heapInv n maxP len' ((p.toNat, size) :: live) 1 ∗ block n p.toNat size) ∨
    (⌜p = 0 ∧ (¬ GrowOk len (some maxP) P ∨ 8 < al.toNat)⌝ ∗ ∃ len', ⌜len' = len ∨ len' = E⌝ ∗
      heapInv n maxP len' live 1))

/-! ## The grown branch -/

theorem pack_grownS {n maxP len E : Nat} {live : List (Nat × Nat)} (hl0 : 0 < len) (hE : len + 65536 ≤ E)
    (hE4 : E % 65536 = 0) (hE32 : E < 2 ^ 32) (hlen0 : len % 65536 = 0)
    (w al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) {size : Nat} (hs0 : 0 < size)
    (hsw : size ≤ 4 * w.toNat) (hfit : 4 * w.toNat + 8 ≤ E - len) (idx : UInt32) (ta a578 : Nat)
    (p : UInt32) (P : Nat) :
    frameH (GF := GF) n maxP len live ∗ n ↦[wmlength] E ∗ n ↦[i32][ len + 4 ] 0 ∗
      (∃ rest : List UInt8, ⌜rest.length = E - len - 12⌝ ∗
        post1 n w al 1074896 (UInt32.ofNat len) (UInt32.ofNat E) 0 true rest 1057464 idx ta a578 [] [.i32 p])
      ⊢ vt n 1057464 idx ta a578 ∗ allocOutS n maxP len E live size al p P := by
  iintro ⟨Hf, Hl, H4, %rest, %hrl, Hp⟩
  iunfold post1 at Hp
  icases Hp with ⟨%r, %hrs, Hvt, Hc⟩
  obtain rfl : p = r := by simpa using hrs
  iframe Hvt
  have hcN : (UInt32.ofNat len).toNat = len := by simp only [UInt32.toNat_ofNat']; omega
  have hEN : (UInt32.ofNat E).toNat = E := by simp only [UInt32.toNat_ofNat']; omega
  have hfits : fits w (UInt32.ofNat len) (UInt32.ofNat E) := by
    unfold fits szN; rw [hcN, hEN]; omega
  iunfold allocOutS
  icases Hc with (⟨%hU, Hs, H0, H8, Hd, -⟩ | ⟨%hW, Hs, H0, H8, Hd, -⟩ | ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, -⟩)
  · -- unlinked: only for misalignment
    have h8 : 8 < al.toNat := by
      rcases hU.2 with h | ⟨-, h⟩
      · exact absurd hfits h
      · by_contra hc
        apply h; unfold aligned; rw [hcN]; exact al_small al k len hal (by omega) hlen0
    ihave Hs := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hs
    ihave H0 := memBytes_addr (b := len) hcN $$ H0
    ihave H8 := memBytes_addr (b := len + 8) (by omega) $$ H8
    ihave Hd := memBytes_addr (b := len + 12) (by omega) $$ Hd
    iright
    isplitr
    · ipureintro; exact ⟨hU.1, Or.inr h8⟩
    iexists E
    isplitr
    · ipureintro; exact Or.inr rfl
    iapply heapInv_mono n maxP E _ 0 1 (by omega)
    iapply pack_U hl0 hE hE4 hE32 rest (by omega)
    iframe Hf Hl H4 Hs H0 H8 Hd
  · -- taken whole
    obtain ⟨hp, hfit', -, hali⟩ := hW
    have hpn : p.toNat = len + 8 := by
      rw [hp, UInt32.toNat_add, hcN, show (8 : UInt32).toNat = 8 from rfl]; omega
    have hfit'' : 4 * w.toNat ≤ E - len - 8 := by
      unfold fits szN at hfit'; rw [hcN, hEN] at hfit'; exact hfit'
    ihave Hs := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hs
    ihave H0 := memBytes_addr (b := len) hcN $$ H0
    ihave H8 := memBytes_addr (b := len + 8) (by omega) $$ H8
    ihave Hd := memBytes_addr (b := len + 12) (by omega) $$ Hd
    ileft
    isplitr
    · ipureintro
      refine ⟨fun h => by rw [h] at hpn; simp at hpn, ?_⟩
      unfold aligned at hali; rw [hcN] at hali; rw [hpn]; exact hali
    iexists E
    isplitr
    · ipureintro; exact Or.inr rfl
    rw [hpn]
    iapply pack_W hl0 hE hE4 hE32 rest (by omega) hs0 (by omega)
    iframe Hf Hl H4 Hs H0 H8 Hd
  · -- split
    obtain ⟨hp, hfit', hcs⟩ := hS
    have hfit'' : 4 * w.toNat ≤ E - len - 8 := by
      unfold fits szN at hfit'; rw [hcN, hEN] at hfit'; exact hfit'
    have hcs' : len + 80 ≤ p.toNat := by unfold canSplit at hcs; rw [hcN, ← hp] at hcs; exact hcs
    have hA1 : p.toNat + 4 * w.toNat ≤ E := by
      have : aN (UInt32.ofNat E) w al ≤ E - 4 * w.toNat := by unfold aN; rw [hEN]; exact Nat.sub_le _ _
      omega
    have hA4 : p.toNat % 4 = 0 := by rw [hp]; exact aN_mod4 _ w al k hal (by rw [hEN]; omega)
    have hAal : p.toNat % al.toNat = 0 := by rw [hp]; exact aN_al _ _ _
    have hw1 : 1 ≤ w.toNat := by omega
    ihave Hs := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hs
    ihave H0 := memBytes_at (b := len) (bs' := bytes32 (UInt32.ofNat (p.toNat - 8))) hcN
      (by rw [sub8_ofNat p (by omega)]) $$ H0
    ihave H8 := memBytes_addr (b := len + 8) (by omega) $$ H8
    ihave Hd := memBytes_addr (b := len + 12) (by omega) $$ Hd
    ihave HN1 := memBytes_addr (b := p.toNat - 8 + 4) (by omega) $$ HN1
    icases HB with ⟨%bs, %hbs, HB⟩
    ileft
    isplitr
    · ipureintro; exact ⟨fun h => by rw [h] at hcs'; simp at hcs', hAal⟩
    iexists E
    isplitr
    · ipureintro; exact Or.inr rfl
    have key := pack_S (GF := GF) (n := n) (maxP := maxP) (live := live) hl0 hE hE4 hE32 (m := p.toNat - 8)
      (size := size) (by omega) (by omega) hs0 (by omega) (by omega)
      (rest.take (p.toNat - 8 - (UInt32.ofNat len).toNat - 12)) (by simp; omega) bs (by rw [hbs, hEN]; omega)
    rw [show p.toNat - 8 + 8 = p.toNat by omega] at key
    iapply key
    iframe Hf Hl H4 Hs H0 H8 Hd HN0 HN1 HB

/-- 581's result for any first walk, packed: `Fr ∗ Z` (what the walk's frame and its
failure leave) give back the heap with an empty list, `W` (its success) packs by `hW`. -/
theorem finishS {n g maxP len : Nat} {live : List (Nat × Nat)} {gt : GlobalType} {sp size al idx : UInt32}
    {ta a578 k : Nat} (Fr Z : IProp GF) (W : UInt32 → UInt32 → IProp GF)
    (hal : al.toNat = 2 ^ k) (hk : k < 20) (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hl0 : 0 < len) (hlen0 : len % 65536 = 0)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hF : Fr ∗ Z ⊢ frameH n maxP len live)
    (hW : ∀ p v : UInt32, p ≠ 0 → (Fr ∗ n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗ W p v ⊢
      vt n 1057464 idx ta a578 ∗ allocOutS n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536)
        live size.toNat al p (cellPages (wordsOf size) al).toNat))
    (p : UInt32) :
    Fr ∗ res581G n g gt sp size al idx ta a578 len maxP Z W p ⊢
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
        n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
      vt n 1057464 idx ta a578 ∗
      allocOutS n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
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
    iunfold allocOutS
    iright
    isplitr
    · ipureintro; exact ⟨hp0, Or.inl hfail⟩
    iexists len
    isplitr
    · ipureintro; exact Or.inl rfl
    iapply heapInv_mono n maxP len live 0 1 (by omega)
    iapply pack_fail
    iframe Hh Hl
    iapply hF
    iframe HF HZ
  · rw [hNX, show pageSize = 65536 from rfl]
    iapply pack_grownS hl0 (by omega) (by omega) (by omega) hlen0 (wordsOf size) al k hal (by omega)
      (by rw [hW']; omega) (by omega) idx ta a578 p
    iframe Hl H4
    isplitl [HF HZ]
    · iapply hF; iframe HF HZ
    iexists rest
    iframe Hpost
    ipureintro; omega

/-! ## A free list of one cell -/

/-- What `heapInv` keeps aside while 581 runs on the one-cell list `[c]` (cells `s ++ c :: t`,
`d` the next neighbour): the limit, the cells before `c`, `c`'s `prev` word, and the cells
after it given back once the next neighbour's `prev` word (`nextW`) is set to some `v`. -/
def frO (n maxP : Nat) (live : List (Nat × Nat)) (s t : List CellM) (c d : CellM) : IProp GF :=
  iprop(n ↪[wmlimit] some maxP ∗ ([∗list] x ∈ s, cellRes n live x) ∗
    n ↦[i32][ c.addr + 4 ] UInt32.ofNat c.prev ∗
    (∀ v : Nat, nextW n (UInt32.ofNat c.next) (UInt32.ofNat v) c.last -∗
      [∗list] x ∈ tS c v d t, cellRes n live x))

/-- 580's leftovers when it unlinks `c`: `c` unchanged, the next neighbour's `prev` word. -/
def zO (n : Nat) (c : CellM) (bs : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ (UInt32.ofNat c.addr).toNat ] w0 (UInt32.ofNat c.next) c.last ∗
    n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] 0 ∗ n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
    nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last)

/-- 580's success on `c`, its slot moved to `ALLOC`. -/
def wO (n : Nat) (w al : UInt32) (c : CellM) (bs : List UInt8) (idx : UInt32) (ta a578 : Nat)
    (r v : UInt32) : IProp GF :=
  iprop(n ↦[i32][ (1074896 : UInt32).toNat ] v -∗
    post1 n w al 1074896 (UInt32.ofNat c.addr) (UInt32.ofNat c.next) (UInt32.ofNat c.addr) c.last bs
      1057464 idx ta a578 [] [.i32 r])

/-- 580's result on `[c]`, as `walkQ`. -/
theorem walkO (n : Nat) (w al slot : UInt32) (c : CellM) (bs : List UInt8) (idx : UInt32) (ta a578 : Nat)
    (args rs : List Value) (hc8 : c.addr + 8 < 2 ^ 32) :
    iprop(emp) ∗ post1 (GF := GF) n w al slot (UInt32.ofNat c.addr) (UInt32.ofNat c.next) (UInt32.ofNat c.addr)
        c.last bs 1057464 idx ta a578 args rs ⊢
      walkQ n slot.toNat idx ta a578 (zO n c bs) (wO n w al c bs idx ta a578) args rs := by
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨-, H⟩
  iunfold post1 at H
  icases H with ⟨%r, %hrs, Hvt, (⟨%hU, Hs, H0, H8, Hd, Hn⟩ | ⟨%hW, Hs, H0, H8, Hd, Hn⟩ |
    ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, Hn⟩)⟩
  · iunfold walkQ; iexists r
    isplitr; · ipureintro; exact hrs
    ileft
    isplitr; · ipureintro; exact hU.1
    iframe Hs Hvt
    iunfold zO
    iframe H0 H8 Hd Hn
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

section One

variable {n maxP len : Nat} {live : List (Nat × Nat)} {H : HeapModel} {s t : List CellM} {c d : CellM}
  (hw : H.wf live 1) (hl : H.len = len) (hc : H.cells = s ++ c :: t)
  (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr)

include hw hc hd in
/-- The next neighbour's `prev` word, out of the cells after `c`. -/
theorem next_open (n : Nat) (live' : List (Nat × Nat)) (hcn : c.next < 2 ^ 32) :
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

variable (hfl : H.freeList = [c.addr]) (hcf : c.allocated = false) (hnf : c.nextFree = 0)

include hw hl hc hd hcf hnf in
/-- 580 unlinked `c`: the heap with an empty free list, `c` leaked. -/
theorem restoreO (bs : List UInt8) (hbs : bs.length + 4 = c.size) :
    frO (GF := GF) n maxP live s t c d ∗ zO n c bs ⊢ frameH n maxP len live := by
  have hg := hw.geo
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hb := hg.bounds c hcc
  have hnx := hg.next_al c hcc
  have hlt := hw.len_lt
  have hcN : (UInt32.ofNat c.addr).toNat = c.addr := by simp only [UInt32.toNat_ofNat']; omega
  iintro ⟨Hfr, Hz⟩
  iunfold zO at Hz
  icases Hz with ⟨H0, H8, Hd, Hn⟩
  iunfold frO at Hfr
  icases Hfr with ⟨#Hm, Hs, H4, Hk⟩
  ihave Ht := Hk $$ %c.addr Hn
  rw [tS_self hw hc hd]
  iunfold frameH
  iexists { H with freeList := [] }
  isplitr
  · ipureintro
    have hg' := hw.geo; have hv' := hw.lives
    exact ⟨⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt, ⟨hg'.bounds, hg'.next_al, hg'.sorted, hg'.next_nb,
      hg'.prev_nb, hg'.first, hg'.disj⟩, AllocFresh.lists_nil rfl, ⟨hv'.live_cell, hv'.cell_live, hv'.live_nodup⟩,
      hw.nf_lo⟩, hl, rfl⟩
  iframe Hm
  rw [show ({ H with freeList := [] } : HeapModel).cells = s ++ c :: t from hc]
  iapply BigSepL.bigSepL_append.2
  iframe Hs
  iapply BigSepL.bigSepL_cons.2
  iframe Ht
  ihave H0 := memBytes_addr hcN $$ H0
  ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
  ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 12 by omega) $$ Hd
  iapply cellRes_free_intro c hcf rfl (word0_free c hcf hnx (by omega)) rfl (by rw [hnf]) bs hbs
  iframe H0 H4 H8 Hd

include hw hl hc hd hcf in
/-- 580 took `c` whole: allocated in place, lent as `(c + 8, size)`, the list emptied. -/
theorem packWO (w al p : UInt32) (hp : p.toNat = c.addr + 8)
    (hfit : 4 * w.toNat ≤ c.next - c.addr - 8) {size : Nat} (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (bs : List UInt8) (hbs : bs.length + 4 = c.size) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[wmlength] len ∗ n ↦[i32][ (1074896 : UInt32).toNat ] 0 ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] 0 ∗ n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs ∗
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
  rw [tS_self hw hc hd, hp]
  ihave Hd := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 12 = c.addr + 8 + 4 by omega) $$ Hd
  ihave H8 := memBytes_addr (show (UInt32.ofNat c.addr).toNat + 8 = c.addr + 8 by omega) $$ H8
  ihave Hd := memBytes_join n (c.addr + 8) 4 (bytes32 0) bs (by simp) $$ [H8 Hd]
  · iframe H8 Hd
  icases memBytes_split n (c.addr + 8) size (bytes32 0 ++ bs) (by simp; omega) $$ Hd with ⟨Hb, Hsl⟩
  isplitr [Hb]
  · iapply heapInv_intro (modelW H s t c) (wf_whole hw hc hcf hs0 (by omega) 1) hl 0
      (by simp [HeapModel.head, modelW])
    ihave Hh := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hh
    iframe Hh Hl Hm
    rw [show (modelW H s t c).cells = s ++ cW c :: t from rfl]
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
      iexists size, (bytes32 0 ++ bs).drop size
      ihave Hsl := memBytes_at (a := c.addr + 8 + size) (b := (cW c).addr + 8 + size) (bs := (bytes32 0 ++ bs).drop size) (bs' := (bytes32 0 ++ bs).drop size) rfl rfl $$ Hsl
      iframe Hsl
      ipureintro
      refine ⟨List.mem_cons_self, ?_⟩
      simp [cW, CellM.size, bytes32]; omega
    iapply bigSep_cons $$ Ht
  · iunfold block
    iexists _
    iframe Hb
    ipureintro; simp; omega

include hw hl hc hd hfl hcf hnf in
/-- 580 split `c` at `p - 8`: `c` shrunk and still listed, the new cell lent as `(p, size)`. -/
theorem packSO (w al p : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) (ha0 : 0 < c.addr)
    (hp : p.toNat = aN (UInt32.ofNat c.next) w al)
    (hfit : 4 * w.toNat ≤ c.next - c.addr - 8) (hcs : c.addr + 80 ≤ p.toNat) (hw1 : 1 ≤ w.toNat)
    {size : Nat} (hs0 : 0 < size) (hsw : size ≤ 4 * w.toNat)
    (bs : List UInt8) (hbs : bs.length + 4 = c.size) :
    frO (GF := GF) n maxP live s t c d ∗ n ↦[wmlength] len ∗
      n ↦[i32][ (1074896 : UInt32).toNat ] UInt32.ofNat c.addr ∗
      n ↦[i32][ (UInt32.ofNat c.addr).toNat ] (p - 8) ∗ n ↦[i32][ (UInt32.ofNat c.addr).toNat + 8 ] 0 ∗
      n ↦[wms][ (UInt32.ofNat c.addr).toNat + 12 ] bs.take (p.toNat - 8 - (UInt32.ofNat c.addr).toNat - 12) ∗
      n ↦[i32][ p.toNat - 8 ] (w0 (UInt32.ofNat c.next) c.last ||| 1) ∗
      n ↦[i32][ p.toNat - 4 ] UInt32.ofNat c.addr ∗
      (∃ bs' : List UInt8, ⌜bs'.length = (UInt32.ofNat c.next).toNat - p.toNat⌝ ∗ n ↦[wms][ p.toNat ] bs') ∗
      nextW n (UInt32.ofNat c.next) (UInt32.ofNat c.addr &&& 3 ||| (p - 8)) c.last
      ⊢ heapInv n maxP len ((p.toNat, size) :: live) 1 ∗ block n p.toNat size := by
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
  have hwf := wf_split hw hc hd hfl hcf hnf ha0 (m := p.toNat - 8) (by omega) (by omega) (by omega)
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
      iapply cellRes_free_intro (cS c (p.toNat - 8)) hcf (a := c.addr) (w0 := UInt32.ofNat (p.toNat - 8)) (w1 := UInt32.ofNat c.prev) (nf := 0) rfl (by simp [cS, CellM.word0, hcf]) rfl
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

end One

end Res

end WNear.Binary.AllocSeq
