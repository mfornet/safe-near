import Bridge.Functions.AllocZeroed
import Bridge.Functions.VecWithCap

/-!
# `__rust_alloc_zeroed` (313 → 239 → 153 → 581 + `memset`) on `heapInv … F`, any `F ≥ 1` (M4)

`AllocZeroed.lean` proves the zeroing allocation on `heapInv … 1` (a single free cell). This file
lifts it to any bound `F ≥ 1` (`VecWithCap.okG`), as `AllocWalkHeap.lean` does for `__rust_alloc`:

* `f581_walk_model`, `f581_spec_walk`: `WeeAlloc::alloc` (581) itself from `heapInv … F`, with
  580's general walk (`AllocWalk.f580_walk`) as the first walk of `AllocGen.f581_genW`:
  `cost581W cfg F size al` (`walkCost cfg F + 610` `regular_op_cost`s and the grow), the bound
  `max F 1`.
* `f581_roomF`: 581 on `heapInv … F`, `okG F`, the bound kept, at `cost581F cfg F size al`
  (`AllocZeroed.cost581` for `F = 1`, `cost581W` above).
* `f153_specF`, `f239_specF`, `f313_specF`: `AllocZeroed`'s proofs with `f581_roomF` in place of
  `f581_room`: a zeroed block (`zeroedPostF`), the bound kept. The cost of `__rust_alloc_zeroed`
  is `costZeroF cfg F size` (for `align = 1`): `costAllocW cfg F size + 33 · regular_op_cost` and
  the `memset`, where `costAllocW` is `__rust_alloc`'s cost by the same route
  (`VecWithCap.costAllocF` but for `F = 2`, which `costAllocF` charges through the two-cell walk:
  `costAllocW_eq`). `costZeroF_one`: at `F = 1` it is `VecFromElem.costAlloc cfg true size`.

The code is `allocCode` and the merge 575 (`code575F`), which the general walk runs.
-/

namespace WNear.Binary.AllocZeroedF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocTwoWalk (code7 code575)
open WNear.Binary.AllocTwo (wf_relen)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocFresh (frameH MFunSpec_frame heapInv_intro)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocGen (res581G pre581G f581_genW MFunSpec_exists)
open WNear.Binary.AllocLimit (growOk_of_room)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocWalk (walkCost zW wW heapW f580_walk allocOutG finishG)
open WNear.Binary.AllocZeroed (allocCode preX cost581 cost153 zeroedPost f581_room heapInv_bound byteOf_zero)
open WNear.Binary.VecWithCap (okG)

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `allocCode` and the merge 575 (persistent): what 581 runs on any free list. -/
def code575F (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(allocCode n maxP inst mi A ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (code575F (GF := GF) n maxP inst mi A) := by
  unfold code575F; infer_instance

end Code

/-! ## `WeeAlloc::alloc` (581) on any free list -/

section Spec581

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of 581 with the general walk over `F` cells. -/
abbrev cost581W (cfg : WasmConfig) (F : Nat) (size al : UInt32) : Nat :=
  walkCost cfg F + 610 * cfg.regularOpCost + cfg.linearOpBaseCost +
    cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat

/-- 581's postcondition before the room is used: `allocOutG`. -/
abbrev post581G (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F' : Nat) : List Value → List Value → IProp GF :=
  fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    vt n 1057464 idx ta a578 ∗
    allocOutG n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p
      (cellPages (wordsOf size) al).toNat F')

set_option maxHeartbeats 4000000 in
/-- `WeeAlloc::alloc(&ALLOC, size, align)` (581) from a model `H` with `H.wf live F`, any `F`:
`allocOutG` with the bound `max F 1`, at `cost581W cfg F size al`. -/
theorem f581_walk_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (H : HeapModel) (hw : H.wf live F) (hl : H.len = len) :
    code575F n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost581W cfg F size al)
        (post581G n g gt sp size al idx ta (A 578) maxP len live (max F 1)) := by
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  iintro #Hk
  iunfold code575F, allocCode at Hk
  icases Hk with ⟨⟨#Hm, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578, #Hi⟩, #H575⟩
  iapply (MFunSpec_frame (Fr := iprop(n ↪[wmlimit] some maxP))
    (P := fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
        pre581G n g gt sp (UInt32.ofNat H.head) len o1 o2 o4 ∗
          (([∗list] c ∈ H.cells, cellRes n live c) ∗ vt n 1057464 idx ta (A 578))))
    (Q := fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581G n g gt sp size al idx ta (A 578) len maxP
      (zW n live F len) (wW n live F len size.toNat al idx ta (A 578)) p)) ?hP ?hQ)
  case hP =>
    intro args
    iintro HX
    iunfold preX at HX
    icases HX with ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hh, Hl, #Hlim, Hc⟩
    isplitl
    · isplitr; · ipureintro; exact ha
      iunfold pre581G
      rw [hl]
      iframe Hg Ho1 Ho2 Ho4 Hh Hl Hc Hvt
    · iexact Hlim
  case hQ =>
    intro args rs
    have hF : iprop(n ↪[wmlimit] some maxP) ∗ zW (GF := GF) n live F len ⊢ frameH n maxP len live := by
      iintro ⟨#Hlim, HZ⟩
      iunfold zW at HZ
      icases HZ with ⟨%H', %⟨hw', hl', hfl'⟩, Hc⟩
      iunfold frameH
      iexists H'
      iframe Hlim Hc
      ipureintro; exact ⟨wf_relen hw' (by rw [hfl']; simp), hl', hfl'⟩
    have hW' : ∀ p v : UInt32, p ≠ 0 → (iprop(n ↪[wmlimit] some maxP) ∗ n ↦[i32][ 1074896 ] v ∗
        n ↦[wmlength] len ∗ wW (GF := GF) n live F len size.toNat al idx ta (A 578) p v ⊢
        vt n 1057464 idx ta (A 578) ∗ allocOutG n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536)
          live size.toNat al p (cellPages (wordsOf size) al).toNat (max F 1)) := by
      intro p v hp0
      iintro ⟨#Hlim, Hh, Hl, HW⟩
      iunfold wW at HW
      icases HW with ⟨Hvt, %hpa, HW⟩
      iunfold heapW at HW
      icases HW with ⟨%H', %⟨hw', hl', hv'⟩, Hc, Hb⟩
      iframe Hvt
      iunfold allocOutG
      ileft
      isplitr; · ipureintro; exact ⟨hp0, hpa⟩
      iexists len
      isplitr; · ipureintro; exact Or.inl rfl
      iframe Hb
      iapply heapInv_mono _ _ _ _ F (max F 1) (le_max_left F 1)
      iapply heapInv_intro H' hw' hl' v hv'
      iframe Hh Hl Hlim Hc
    iintro ⟨#Hlim, %p, %hrs, HR⟩
    iexists p
    isplitr; · ipureintro; exact hrs
    iapply (finishG (n := n) (g := g) (live := live) (k := k) (F' := max F 1) iprop(n ↪[wmlimit] some maxP)
      (zW n live F len) (wW n live F len size.toNat al idx ta (A 578)) (le_max_right F 1) hal hk hsize hsize2
      hlen1 hlen0 hroom hF hW' p)
    iframe Hlim HR
  iapply (f581_genW cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al (UInt32.ofNat H.head) idx k len
    maxP o1 o2 o4 (iprop(([∗list] c ∈ H.cells, cellRes n live c) ∗ vt n 1057464 idx ta (A 578)))
    (zW n live F len) (wW n live F len size.toNat al idx ta (A 578)) (walkCost cfg F)
    hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom)
  iframe Hm H570 H568 H580 H577 H572 H569 H573 H574 H576 H578 Hi
  iapply (f580_walk cfg lim (d + 1) types[34]! (by rfl) inst mi n hm.mem (A 572) (A 575) (A 576) (A 574)
    (A 578) ta (hm.funcs 572 (by decide)) (hm.funcs 575 (by decide)) (hm.funcs 576 (by decide))
    (hm.funcs 574 (by decide)) hm.table types[32]! types[0]! types[32]! types[0]!
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rw [hm.types]; rfl) (by rw [hm.types]; rfl) (by omega) Cg
    (wordsOf size) al (UInt32.ofNat (sp.toNat - 4)) idx k hal (by omega) (by rw [hW]; omega) (by rw [hW]; omega)
    maxP len live F size.toNat (by omega) (by rw [hW]; omega) H hw hl)
  iunfold code7
  iunfold code575
  rw [hm.types]
  iframe H572 H576 H574 H578 Hi H575 Hm

/-- **`WeeAlloc::alloc(&ALLOC, size, align)` (581) on `heapInv … F`, any `F`, with room**: a block
`p ≠ 0` (aligned), `heapInv … ((p, size) :: live) (max F 1)`, at `cost581W cfg F size al`. -/
theorem f581_spec_walk (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    code575F n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => cost581W cfg F size al)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) (max F 1) ∗ block n p.toNat size.toNat)) := by
  have hok := growOk_of_room len _ maxP hlen0 hroom hmax
  have hk : k < 20 := by
    by_contra hc
    have : 2 ^ 20 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  iintro #Hc
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ x : {H : HeapModel // H.wf live F ∧ H.len = len},
      preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al x.1 args))
    (Q := post581G n g gt sp size al idx ta (A 578) maxP len live (max F 1)) ?hP1 ?hQ1)
  case hP1 =>
    intro args
    iintro ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
    iunfold heapInv at Hinv
    icases Hinv with ⟨%H, %⟨hw, hl⟩, Hh, Hl, #Hlim, Hcs⟩
    isplitl
    · iexists ⟨H, hw, hl⟩
      iunfold preX
      ihave Hh := memBytes_addr (a := headAddr) (b := 1074896) rfl $$ Hh
      iframe Hg Ho1 Ho2 Ho4 Hvt Hh Hl Hlim Hcs
      ipureintro; exact ha
    · iempintro
  case hQ1 =>
    intro args rs
    iintro ⟨-, %p, %hrs, Hg, Hst, Hvt, HO⟩
    iunfold allocOutG at HO
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
  iapply MFunSpec_exists
  imodintro
  iintro %x
  obtain ⟨H, hw, hl⟩ := x
  iapply (f581_walk_model cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k maxP len live F
    o1 o2 o4 hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H hw hl)
  iexact Hc

/-- The cost of 581 on `heapInv … F`: `AllocZeroed.cost581` (the one-cell walks) for `F = 1`, the
general walk's `cost581W` above. -/
def cost581F (cfg : WasmConfig) (F : Nat) (size al : UInt32) : Nat :=
  if F = 1 then cost581 cfg size al else cost581W cfg F size al

/-- 581 on `heapInv … F`, `okG F`, with room: a block, the bound `F` kept, at `cost581F`. -/
theorem f581_roomF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) (hF : okG F) :
    code575F n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => cost581F cfg F size al)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) F ∗ block n p.toNat size.toNat)) := by
  unfold okG at hF
  by_cases h1 : F = 1
  · subst h1
    rw [show (fun _ : List Value => cost581F cfg 1 size al) = (fun _ => 910 * cfg.regularOpCost +
        cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat) from by
      funext _; simp [cost581F, cost581]]
    iintro #Hc
    iunfold code575F at Hc
    icases Hc with ⟨#Hc, -⟩
    iapply (f581_room cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k maxP len live
      o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax)
    iexact Hc
  · rw [show (fun _ : List Value => cost581F cfg F size al) = (fun _ => cost581W cfg F size al) from by
      funext _; simp [cost581F, h1]]
    have key := f581_spec_walk (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k
      maxP len live F o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax
    rw [Nat.max_eq_left hF] at key
    exact key

end Spec581

/-! ## The zeroing allocation (153, 239, 313) on any free list -/

section Zeroed

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `AllocZeroed.zeroedPost` on `heapInv … F`. -/
def zeroedPostF (n g : Nat) (gt : GlobalType) (sp size al idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
    g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
      n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
    vt n 1057464 idx ta a578 ∗
    ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
      heapInv n maxP len' ((p.toNat, size.toNat) :: live) F ∗
      n ↦[wms][ p.toNat ] List.replicate size.toNat 0)

/-- The cost of `alloc_zeroed` (153) on `heapInv … F`. -/
def cost153F (cfg : WasmConfig) (F : Nat) (size al : UInt32) : Nat :=
  34 * cfg.regularOpCost + cost581F cfg F size al + MemSet.cost size.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- `GlobalAlloc::alloc_zeroed` (153) on `heapInv … F`: 581, then `memset(p, 0, size)`. -/
theorem f153_specF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) (hF : okG F) :
    code575F n maxP inst mi A ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f153 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => cost153F cfg F size al)
        (zeroedPostF n g gt sp size al idx ta (A 578) maxP len live F) := by
  iintro ⟨#Hcode, #H581, #H952⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code575F, allocCode at Hcode
    icases Hcode with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have ha581 := hm.funcs 581 (by decide)
  have ha952 := hm.funcs 952 (by decide)
  have hn := hm.mem
  have t15 : types[15]!.params.length = 3 := by rfl
  have h581 := f581_roomF (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt sp
    size al idx k maxP len live F o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax hF
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
  subst hargs
  simp only [f153, cost153F]
  generalize cost581F cfg F size al = K581 at h581 ⊢
  mstep; mstep; mstep; mstep
  mcall h581 using [Hg Ho1 Ho2 Ho4 Hvt Hinv]
    with (simp [activationGas, entryLocals, f581]; omega)
  · iframe Hg Ho1 Ho2 Ho4 Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0, hpa⟩, Hg, Hst, Hvt, %len', %hl', Hinv, Hb⟩
  subst hrs
  ihave Hinv := heapInv_bound n maxP len' _ F $$ Hinv
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
  iunfold zeroedPostF
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

set_option maxRecDepth 100000 in
/-- `__rg_alloc_zeroed` (239) on `heapInv … F`: `alloc_zeroed(&ALLOC, size, align)`. -/
theorem f239_specF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) (hF : okG F) :
    code575F n maxP inst mi A ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 153 ↪[wf] FuncInst.wasm types[15]! inst f153
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f239 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => 14 * cfg.regularOpCost + cost153F cfg F size al)
        (zeroedPostF n g gt sp size al idx ta (A 578) maxP len live F) := by
  iintro ⟨#Hcode, #H581, #H952, #H153⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code575F, allocCode at Hcode
    icases Hcode with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have ha153 := hm.funcs 153 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have h153 := f153_specF (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt sp size al idx k maxP len live F o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax hF
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
  subst hargs
  simp only [f239]
  generalize cost153F cfg F size al = K at h153 ⊢
  mstep; mstep; mstep
  mcall h153 using [Hg Ho1 Ho2 Ho4 Hvt Hinv]
    with (simp [activationGas, entryLocals, f153, ]; omega)
  · iframe Hg Ho1 Ho2 Ho4 Hvt Hinv
  iunfold zeroedPostF at HQ
  icases HQ with ⟨%p, %⟨hrs, hp0, hpa⟩, HQ⟩
  subst hrs
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold zeroedPostF
  iexists p
  iframe HQ
  ipureintro; exact ⟨by simp [htype], hp0, hpa⟩

set_option maxRecDepth 100000 in
/-- **`__rust_alloc_zeroed(size, align)`** (313 → 239 → 153 → 581, `memset`) on `heapInv … F`,
`okG F`, with room: a zeroed block (`zeroedPostF`), the bound kept. -/
theorem f313_specF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hal8 : al.toNat ≤ 8)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) (hF : okG F) :
    code575F n maxP inst mi A ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 153 ↪[wf] FuncInst.wasm types[15]! inst f153 ∗
      A 239 ↪[wf] FuncInst.wasm types[13]! inst f239
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f313 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => 15 * cfg.regularOpCost + (14 * cfg.regularOpCost + cost153F cfg F size al))
        (zeroedPostF n g gt sp size al idx ta (A 578) maxP len live F) := by
  iintro ⟨#Hcode, #H581, #H952, #H153, #H239⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code575F, allocCode at Hcode
    icases Hcode with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have ha239 := hm.funcs 239 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have h239 := f239_specF (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt sp size al idx k maxP len live F o1 o2 o4 hsp hal hal8 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax hF
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
  subst hargs
  simp only [f313]
  generalize 14 * cfg.regularOpCost + cost153F cfg F size al = K at h239 ⊢
  mstep; mstep
  mcall h239 using [Hg Ho1 Ho2 Ho4 Hvt Hinv]
    with (simp [activationGas, entryLocals, f239, ]; omega)
  · iframe Hg Ho1 Ho2 Ho4 Hvt Hinv
  iunfold zeroedPostF at HQ
  icases HQ with ⟨%p, %⟨hrs, hp0, hpa⟩, HQ⟩
  subst hrs
  mcredits (3 * cfg.regularOpCost + R)
  mstep; mstep; mstep
  mcredits R
  iframe Hc
  iunfold zeroedPostF
  iexists p
  iframe HQ
  ipureintro; exact ⟨by simp [htype], hp0, hpa⟩

/-! ## The cost, against `__rust_alloc`'s -/

/-- `__rust_alloc(size, 1)`'s cost by the route of `f581_roomF`: `VecFromElem.costAlloc cfg false`
for `F = 1`, the general walk's `AllocWalk.cost310W` above. -/
def costAllocW (cfg : WasmConfig) (F : Nat) (size : UInt32) : Nat :=
  if F = 1 then VecFromElem.costAlloc cfg false size else AllocWalk.cost310W cfg F size 1

/-- It is `VecWithCap.costAllocF` but for `F = 2` (where `costAllocF` takes the two-cell walk). -/
theorem costAllocW_eq (cfg : WasmConfig) {F : Nat} (hF : okG F) (h : F ≠ 2) (size : UInt32) :
    costAllocW cfg F size = VecWithCap.costAllocF cfg F size := by
  unfold costAllocW VecWithCap.costAllocF
  unfold okG at hF
  by_cases h1 : F = 1
  · subst h1; simp
  · have h3 : ¬ F ≤ 2 := by omega
    simp [h1, h3]

/-- **The cost of `__rust_alloc_zeroed(size, 1)` on `heapInv … F`**: `__rust_alloc`'s
(`costAllocW`), 33 `regular_op_cost`s more, and the `memset`. -/
def costZeroF (cfg : WasmConfig) (F : Nat) (size : UInt32) : Nat :=
  15 * cfg.regularOpCost + (14 * cfg.regularOpCost + cost153F cfg F size 1)

theorem costZeroF_eq (cfg : WasmConfig) (F : Nat) (size : UInt32) :
    costZeroF cfg F size =
      costAllocW cfg F size + 33 * cfg.regularOpCost + MemSet.cost size.toNat * cfg.regularOpCost := by
  unfold costZeroF cost153F cost581F costAllocW
  by_cases h1 : F = 1
  · simp [h1, VecFromElem.costAlloc]; omega
  · simp [h1, AllocWalk.cost310W, cost581W]; omega

/-- At `F = 1`, the cost of `AllocZeroed.f313_spec_room` (`VecFromElem.costAlloc cfg true`). -/
theorem costZeroF_one (cfg : WasmConfig) (size : UInt32) :
    costZeroF cfg 1 size = VecFromElem.costAlloc cfg true size := by
  simp [costZeroF, cost153F, cost581F, VecFromElem.costAlloc, cost153]

end Zeroed

end WNear.Binary.AllocZeroedF
