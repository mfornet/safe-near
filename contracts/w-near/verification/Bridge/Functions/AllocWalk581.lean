import Bridge.Functions.AllocWalkHeap
import Bridge.Functions.AllocZeroed

/-!
# `WeeAlloc::alloc` (581) on `heapInv … F` for any `F` (M4)

`AllocWalkHeap.f310_spec_walk` at the level of 581, for the callers that reach the allocator
without `__rust_alloc` (`__rust_realloc`'s 154 calls `581(&ALLOC, size, align)` directly):
`f581_walk_model` and `f581_spec_walk` are `f310_walk_model` and `f310_spec_walk` with
`AllocWalkGen.f581_genW` in place of `f310_genW`, the 30 `regular_op_cost`s of the wrappers
less (`cost581W`).
-/

namespace WNear.Binary.AllocWalk

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeq
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocTwoWalk (code7 code575)
open WNear.Binary.AllocTwo (code310 wf_relen)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages cellPages_bounds shl16_toNat)
open WNear.Binary.AllocFresh (frameH MFunSpec_frame pack_fail heapInv_intro)
open WNear.Binary.AllocAlloc (wordsOf chunkEnd)
open WNear.Binary.AllocGen (walkQ walkSpecW res581G pre581G f581_genW MFunSpec_exists)
open WNear.Binary.AllocLimit (growOk_of_room)
open WNear.Binary.Interface (IfaceMod)

section Spec581

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of `WeeAlloc::alloc` (581) on `heapInv … F`: `cost310W` without the wrappers. -/
abbrev cost581W (cfg : WasmConfig) (F : Nat) (size al : UInt32) : Nat :=
  walkCost cfg F + 610 * cfg.regularOpCost + cfg.linearOpBaseCost +
    cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat

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
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f581 Cg
        (AllocZeroed.preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al H)
        (fun _ => cost581W cfg F size al)
        (postG n g gt sp size al idx ta (A 578) maxP len live (max F 1)) := by
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  iintro #Hk
  iunfold code310 at Hk
  icases Hk with ⟨#Hm, #H236, #H581, #H570, #H568, #H580, #H577, #H572, #H569, #H573, #H574, #H576, #H578,
    #H575, #Hi⟩
  iapply (MFunSpec_frame (Fr := iprop(n ↪[wmlimit] some maxP))
    (P := fun args => iprop(⌜args = [.i32 1074896, .i32 size, .i32 al]⌝ ∗
        (pre581G n g gt sp (UInt32.ofNat H.head) len o1 o2 o4 ∗
          (([∗list] c ∈ H.cells, cellRes n live c) ∗ vt n 1057464 idx ta (A 578)))))
    (Q := fun _ rs => iprop(∃ p, ⌜rs = [.i32 p]⌝ ∗ res581G n g gt sp size al idx ta (A 578) len maxP
      (zW n live F len) (wW n live F len size.toNat al idx ta (A 578)) p)) ?hP ?hQ)
  case hP =>
    intro args
    iintro HX
    iunfold AllocZeroed.preX at HX
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

/-- **`WeeAlloc::alloc(&ALLOC, size, align)` (581) on `heapInv … F`, any `F`, with room**: a
block `p ≠ 0` (aligned), `heapInv … ((p, size) :: live) (max F 1)`, at `cost581W cfg F size al`. -/
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
    code310 n maxP inst mi A
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
      AllocZeroed.preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al x.1 args))
    (Q := postG n g gt sp size al idx ta (A 578) maxP len live (max F 1)) ?hP1 ?hQ1)
  case hP1 =>
    intro args
    iintro ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
    iunfold heapInv at Hinv
    icases Hinv with ⟨%H, %⟨hw, hl⟩, Hh, Hl, #Hlim, Hcs⟩
    isplitl
    · iexists ⟨H, hw, hl⟩
      iunfold AllocZeroed.preX
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

end Spec581

end WNear.Binary.AllocWalk
