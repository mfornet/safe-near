import Bridge.Functions.AllocTwoSeq

/-!
# `__rust_alloc` on `heapInv … F`, `F ≤ 2`, with room (M4)

`f310_spec_two`: the heap-level form of `AllocTwo.f310_two_model`. From `heapInv n maxP len live F`
with `F ≤ 2`, `__rust_alloc(size, 1)` with room under the limit (`E / 65536 ≤ maxP`) returns a
block `p ≠ 0` and `heapInv … ((p, size) :: live) 2`, at the cost of `AllocSeq.f310_spec_room`.

The model's degenerate case `f310_two_model` excludes (`hdeg`: a list `[a, 0]`) is impossible
since `HeapModel.wf` has `mem0_pos`: a listed cell lies at an address `≥ mem0 > 0`.
-/

namespace WNear.Binary.AllocTwo

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv WNear.Binary.AllocSeq
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocDealloc (nodup_of_sorted cellAt_iff')
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocGen (MFunSpec_exists)
open WNear.Binary.AllocLimit (growOk_of_room)
open WNear.Binary.Interface (IfaceMod)

/-- No listed cell at address 0 (`mem0_pos`): `f310_two_model`'s `hdeg`. -/
theorem no_deg {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) :
    ∀ a ca, H.freeList = [a, 0] → H.cellAt a = some ca → ca.nextFree % 2 = 0 := by
  intro a ca hfl _
  exfalso
  obtain ⟨c, hc, -⟩ := hw.lists.fl_free 0 (by rw [hfl]; simp)
  obtain ⟨hcm, hca⟩ := (cellAt_iff' (nodup_of_sorted hw.geo.sorted)).mp hc
  have := (hw.geo.bounds c hcm).1
  have := hw.mem0_pos
  omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`__rust_alloc(size, 1)` on `heapInv … F`, `F ≤ 2`, with room**: a block, `heapInv … 2`. -/
theorem f310_spec_two (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal1 : al.toNat = 1) (hF : F ≤ 2)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32)
    (hmax : (len + (cellPages (wordsOf size) al).toNat * 65536) / 65536 ≤ maxP) :
    code310 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => cost310 cfg size al)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) al).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) 2 ∗ block n p.toNat size.toNat)) := by
  have hok := growOk_of_room len _ maxP hlen0 hroom hmax
  iintro #Hc
  iapply (MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(∃ x : {H : HeapModel // H.wf live 2 ∧ H.len = len},
      preX n g gt sp o1 o2 o4 idx ta (A 578) maxP live size al x.1 args))
    (Q := postT n g gt sp size al idx ta (A 578) maxP len live) ?hP1 ?hQ1)
  case hP1 =>
    intro args
    iintro ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
    ihave Hinv := heapInv_mono n maxP len live F 2 hF $$ Hinv
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
    iunfold allocOut2 at HO
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
  iapply (f310_two_model cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx maxP len live
    o1 o2 o4 hsp hal1 hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom H hw hl (no_deg hw))
  iexact Hc

end Spec

end WNear.Binary.AllocTwo
