import Bridge.Functions.AllocSeq
import Bridge.Functions.MemSet

/-!
# `__rust_alloc_zeroed` (313 → 239 → 153 → 581 + `memset`) on `heapInv … 1` (M4)

```wat
(func 313 (param size align) (result i32) (local r)   ;; __rust_alloc_zeroed
  local.get 0  local.get 1  call 239  local.set 2  local.get 2  return)
(func 239 (param size align) (result i32)             ;; __rg_alloc_zeroed
  i32.const 1074896  local.get 0  local.get 1  call 153)
(func 153 (param alloc size align) (result i32)       ;; GlobalAlloc::alloc_zeroed
  block
    local.get 0  local.get 1  local.get 2  call 581  local.tee 0
    i32.eqz  br_if 0
    local.get 0  i32.const 0  local.get 1  call 952  drop
  end
  local.get 0)
```

* `f581_spec_seq`, `f581_spec_room`: `WeeAlloc::alloc` (581) itself on `heapInv … 1`,
  as `AllocSeq.f310_spec_seq` / `f310_spec_room` (the same proof, `AllocGen.f581_gen` in
  place of `f581_gen`): `910` `regular_op_cost`s plus the grow.
* `f153_spec_room`, `f239_spec_room`, `f313_spec_room`: with room (`E / 65536 ≤ maxP`,
  `align ≤ 8`, `1 ≤ size < 2^28`), the result is a zeroed block: `p ≠ 0`, aligned,
  `p ↦ replicate size 0`, `(p, size)` live in `heapInv … 1` (`zeroedPost`).
  Costs (activation of the callee excluded, as for every `MFunSpec`): 153
  `34 + cost581 + MemSet.cost size`, 239 `14 +` that, 313 `15 +` that.
-/

namespace WNear.Binary.AllocZeroed

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeqModel WNear.Binary.AllocSeq
open WNear.Binary.AllocFirstFit (post1 vt w0 aN fits canSplit aligned szN oneRes nextW f580_empty f580_one
  and3_of_mod4)
open WNear.Binary.AllocDealloc (cellRes_free memBytes_at nodup_of_sorted cellAt_iff')
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq cellPages)
open WNear.Binary.AllocFresh (frameH MFunSpec_frame)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocGen (walkQ walkSpec res581G pre581G f581_gen MFunSpec_cost MFunSpec_exists)
open WNear.Binary.AllocLimit (growOk_of_room)
open WNear.Binary.Interface (IfaceMod)

section Spec581

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of 581 with the heap's model `H` out. -/
def preX (n g : Nat) (gt : GlobalType) (sp : UInt32) (o1 o2 o4 : List UInt8) (idx : UInt32) (ta a578 maxP : Nat)
    (live : List (Nat × Nat)) (size al : UInt32) (H : HeapModel) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ sp.toNat - 16 ] o1 ∗
    n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ 1074896 ] UInt32.ofNat H.head ∗ n ↦[wmlength] H.len ∗ n ↪[wmlimit] some maxP ∗
    [∗list] c ∈ H.cells, cellRes n live c)

set_option maxHeartbeats 4000000 in
/-- `WeeAlloc::alloc(&ALLOC, size, align)` (581) on the heap any sequence of allocations
leaves (`heapInv … 1`), holding the memory's limit (see the module doc). -/
theorem f581_spec_seq (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    n ↪[wmlimit] some maxP ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          allocOutS n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
            (cellPages (wordsOf size) al).toNat)) := by
  iintro ⟨#Hm, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩
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
      exact ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, ⟨hg'.bounds, hg'.next_al, hg'.sorted, hg'.next_nb,
        hg'.prev_nb, hg'.first, hg'.disj⟩, AllocFresh.lists_nil rfl, ⟨hv'.live_cell, hv'.cell_live,
        hv'.live_nodup⟩, hw.nf_lo⟩
    iapply (MFunSpec_frame (Fr := frameH n maxP len live)
      (P := fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
        (pre581G n g gt sp 0 len o1 o2 o4 ∗ vt n 1057464 idx ta (A 578))))
      (Q := postG n g gt sp size al idx ta (A 578) len maxP iprop(emp) (fun _ _ => iprop(⌜False⌝))) ?hPE ?hQE)
    case hPE =>
      intro args
      iintro HX
      iunfold preX at HX
      icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
      isplitr [Hc]
      · isplitr; · ipureintro; exact ha
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
    iapply (f581_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al 0 idx k len maxP o1 o2 o4
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
      iapply (f580_empty cfg lim (d + 1) types[34]! (by rfl) inst mi n hm.mem Cg (wordsOf size) al
        (UInt32.ofNat (sp.toNat - 4)) 1057464 1057464)
    iframe H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi
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
        (⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp (UInt32.ofNat c.addr) len o1 o2 o4 ∗ pwO n c y.1 idx ta (A 578))) ∗
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
      (P := fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
          (pre581G n g gt sp (UInt32.ofNat c.addr) len o1 o2 o4 ∗ pwO n c bs idx ta (A 578))))
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
    iapply (f581_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al (UInt32.ofNat c.addr) idx k
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
      iapply (f580_one cfg lim (d + 1) types[34]! (by rfl) inst mi n hm.mem (A 572) (A 576) (A 574) (A 578) ta
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
    iframe H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi



/-- `WeeAlloc::alloc` (581) with room: under the limit (`E / 65536 ≤ maxP`) and `align ≤ 8`, the
result is a block. -/
theorem f581_spec_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    n ↪[wmlimit] some maxP ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
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
  refine (f581_spec_seq cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k maxP len live
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


end Spec581

section Zeroed

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The allocator's code below 581 and the memory's limit (persistent): `f581_spec_room`'s
premises. -/
def allocCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(n ↪[wmlimit] some maxP ∗
    A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
    A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
    A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
    A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
    A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
    inst ↪[inst] mi)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (allocCode (GF := GF) n maxP inst mi A) := by
  unfold allocCode; infer_instance

/-- The live blocks lie below the memory's length, itself below `2^32`. -/
theorem heapInv_bound (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) :
    heapInv (GF := GF) n maxP len live F ⊢
      ⌜(∀ p s, (p, s) ∈ live → p + s ≤ len) ∧ len < 2 ^ 32⌝ ∗ heapInv n maxP len live F := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hw, hl⟩, Hh, Hl, Hm, Hc⟩
  isplitr
  · ipureintro
    refine ⟨fun p s hps => ?_, hl ▸ hw.len_lt⟩
    obtain ⟨-, c, hc, -, hp, hs⟩ := hw.lives.live_cell p s hps
    have hb := hw.geo.bounds c hc
    simp only [CellM.size] at hs
    omega
  iunfold heapInv
  iexists M
  iframe Hh Hl Hm Hc
  ipureintro; exact ⟨hw, hl⟩

/-- `f581_spec_room` from the bundled code. -/
theorem f581_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    allocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) 1 ∗ block n p.toNat size.toNat)) := by
  iintro Hc
  iunfold allocCode at Hc
  iapply (f581_spec_room cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k maxP len live
    o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax)
  iexact Hc

/-- What a zeroing allocation leaves: a nonzero aligned `p`, the shadow-stack words, the
policy's vtable slot, and the heap with `(p, size)` live, its bytes zero. -/
def zeroedPost (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (_args rs : List Value) : IProp GF :=
  iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
    g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    vt n 1057464 idx ta a578 ∗
    ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
      heapInv n maxP len' ((p.toNat, size.toNat) :: live) 1 ∗
      n ↦[wms][ p.toNat ] List.replicate size.toNat 0)

theorem byteOf_zero : MemSet.byteOf 0 = 0 := by decide

/-- The cost of 581 (with its grow). -/
def cost581 (cfg : WasmConfig) (size al : UInt32) : Nat :=
  910 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- `GlobalAlloc::alloc_zeroed` (153): 581, then `memset(p, 0, size)`. -/
theorem f153_spec_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    allocCode n maxP inst mi A ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f153 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 34 * cfg.regularOpCost + cost581 cfg size al +
          MemSet.cost size.toNat * cfg.regularOpCost)
        (zeroedPost n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro ⟨#Hcode, #H581, #H952⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold allocCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha581 := hm.funcs 581 (by decide)
  have ha952 := hm.funcs 952 (by decide)
  have hn := hm.mem
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
  subst hargs
  simp only [f153, cost581]
  mstep; mstep; mstep; mstep
  mcall (f581_room cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt sp size al idx k
      maxP len live o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax)
    using [Hg Ho1 Ho2 Ho4 Hvt Hinv]
  · iframe Hg Ho1 Ho2 Ho4 Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0, hpa⟩, Hg, Hst, Hvt, %len', %hl', Hinv, Hb⟩
  subst hrs
  ihave Hinv := heapInv_bound n maxP len' _ 1 $$ Hinv
  icases Hinv with ⟨%⟨hbd, hl32⟩, Hinv⟩
  have hpb := hbd p.toNat size.toNat (List.mem_cons_self ..)
  iunfold block at Hb
  icases Hb with ⟨%bs, %hbs, Hb⟩
  mstep; mstep; mstep
  mstep; mstep; mstep
  have h952 := MemSet.f952_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg p 0 size bs hbs
    (by omega)
  generalize MemSet.cost size.toNat * cfg.regularOpCost = MC at h952 ⊢
  mcall h952
    using [Hb] with (simp [activationGas, entryLocals, f952, ]; omega)
  · iunfold MemSet.pre
    iframe Hb
    ipureintro; rfl
  iunfold MemSet.post at HQ
  icases HQ with ⟨%hrs, Hb⟩
  subst hrs
  mcredits (2 * cfg.regularOpCost + R)
  mstep; mstep
  mcredits R
  iframe Hc
  iunfold zeroedPost
  iexists p
  isplitr
  · ipureintro; exact ⟨by simp [htype], hp0, hpa⟩
  iframe Hg Hst Hvt
  iexists len'
  iframe Hinv
  isplitr
  · ipureintro; exact hl'
  rw [byteOf_zero]
  iexact Hb

/-- The cost of `alloc_zeroed` (153) of `size` bytes. -/
def cost153 (cfg : WasmConfig) (size al : UInt32) : Nat :=
  34 * cfg.regularOpCost + cost581 cfg size al + MemSet.cost size.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
/-- `__rg_alloc_zeroed` (239): `alloc_zeroed(&ALLOC, size, align)`. -/
theorem f239_spec_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
    allocCode n maxP inst mi A ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 153 ↪[wf] FuncInst.wasm types[15]! inst f153
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f239 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 14 * cfg.regularOpCost + cost153 cfg size al)
        (zeroedPost n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro ⟨#Hcode, #H581, #H952, #H153⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold allocCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha153 := hm.funcs 153 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have h153 := f153_spec_room (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt sp size al idx k maxP len live o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
  subst hargs
  simp only [f239, cost153]
  generalize 34 * cfg.regularOpCost + cost581 cfg size al + MemSet.cost size.toNat * cfg.regularOpCost = K
    at h153 ⊢
  mstep; mstep; mstep
  mcall h153 using [Hg Ho1 Ho2 Ho4 Hvt Hinv]
    with (simp [activationGas, entryLocals, f153, ]; omega)
  · iframe Hg Ho1 Ho2 Ho4 Hvt Hinv
  iunfold zeroedPost at HQ
  icases HQ with ⟨%p, %⟨hrs, hp0, hpa⟩, HQ⟩
  subst hrs
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold zeroedPost
  iexists p
  iframe HQ
  ipureintro; exact ⟨by simp [htype], hp0, hpa⟩

set_option maxRecDepth 100000 in
/-- **`__rust_alloc_zeroed(size, align)`** (313 → 239 → 153 → 581, `memset`) with room:
a zeroed block (`zeroedPost`). -/
theorem f313_spec_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    allocCode n maxP inst mi A ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 153 ↪[wf] FuncInst.wasm types[15]! inst f153 ∗
      A 239 ↪[wf] FuncInst.wasm types[13]! inst f239
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f313 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 15 * cfg.regularOpCost + (14 * cfg.regularOpCost + cost153 cfg size al))
        (zeroedPost n g gt sp size al idx ta (A 578) maxP len live) := by
  iintro ⟨#Hcode, #H581, #H952, #H153, #H239⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold allocCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha239 := hm.funcs 239 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have h239 := f239_spec_room (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt sp size al idx k maxP len live o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
  subst hargs
  simp only [f313]
  generalize 14 * cfg.regularOpCost + cost153 cfg size al = K at h239 ⊢
  mstep; mstep
  mcall h239 using [Hg Ho1 Ho2 Ho4 Hvt Hinv]
    with (simp [activationGas, entryLocals, f239, ]; omega)
  · iframe Hg Ho1 Ho2 Ho4 Hvt Hinv
  iunfold zeroedPost at HQ
  icases HQ with ⟨%p, %⟨hrs, hp0, hpa⟩, HQ⟩
  subst hrs
  mcredits (3 * cfg.regularOpCost + R)
  mstep; mstep; mstep
  mcredits R
  iframe Hc
  iunfold zeroedPost
  iexists p
  iframe HQ
  ipureintro; exact ⟨by simp [htype], hp0, hpa⟩

end Zeroed

end WNear.Binary.AllocZeroed
