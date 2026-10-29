import Bridge.Functions.AllocInv

/-! # Reordering the allocator's logical live-allocation list -/

namespace WNear.Binary.AllocInv

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-- Live allocations are a set with unique pointers; their enumeration order is immaterial. -/
theorem HeapModel.wf.live_perm {H : HeapModel} {live live' : List (Nat × Nat)} {F : Nat}
    (hw : H.wf live F) (hp : live.Perm live') : H.wf live' F := by
  refine { hw with lives := ⟨?_, ?_, ?_⟩ }
  · intro p s hs
    exact hw.lives.live_cell p s (hp.mem_iff.mpr hs)
  · intro c hc ha
    obtain ⟨s, hs⟩ := hw.lives.cell_live c hc ha
    exact ⟨s, hp.mem_iff.mp hs⟩
  · exact (hp.map Prod.fst).nodup_iff.mp hw.lives.live_nodup

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Reordering live allocations changes no physical cell resource. -/
theorem cellRes_perm (n : Nat) (live live' : List (Nat × Nat)) (c : CellM) (hp : live.Perm live') :
    cellRes (GF := GF) n live c ⊢ cellRes n live' c := by
  iintro H
  iunfold cellRes at H
  iunfold cellRes
  icases H with ⟨H0, H4, Hd⟩
  iframe H0 H4
  by_cases ha : c.allocated = true
  · simp only [ha, ite_true]
    icases Hd with ⟨%s, %bs, %⟨hs, hlen⟩, Hb⟩
    iexists s, bs
    iframe Hb
    ipureintro; exact ⟨hp.mem_iff.mp hs, hlen⟩
  · have hf : c.allocated = false := Bool.eq_false_iff.mpr ha
    simp only [hf, Bool.false_eq_true, ite_false]
    iexact Hd

/-- The heap invariant is invariant under permutation of its logical live list. -/
theorem heapInv_perm (n maxP len : Nat) (live live' : List (Nat × Nat)) (F : Nat)
    (hp : live.Perm live') : heapInv (GF := GF) n maxP len live F ⊢ heapInv n maxP len live' F := by
  iintro H
  iunfold heapInv at H
  iunfold heapInv
  icases H with ⟨%M, %⟨hw, hlen⟩, Hhead, Hlen, Hmax, Hcells⟩
  iexists M
  isplitr
  · ipureintro; exact ⟨hw.live_perm hp, hlen⟩
  iframe Hhead Hlen Hmax
  iapply BigSepL.bigSepL_mono (fun _ => cellRes_perm n live live' _ hp)
  iexact Hcells

end Resource
end WNear.Binary.AllocInv
