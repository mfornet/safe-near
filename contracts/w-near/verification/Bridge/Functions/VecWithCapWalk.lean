import Bridge.Functions.VecWithCap
import Bridge.Functions.AllocWalkHeap

/-!
# `__rust_alloc(size, 1)` on `heapInv … F` for any `F ≥ 1`, as the `RawVec` chain calls it (M4)

`VecWithCap.f310_roomF` allocates on `heapInv … F` for `F ∈ {1, 2}` (`okF`) at a cost independent
of `F` (`costAlloc cfg false size`). `f310_roomG` allocates for any `F ≥ 1` (`okG`), keeping the
bound, at `costAllocF cfg F size`: `costAlloc cfg false size` for `F ≤ 2` (through `f310_roomF`),
`AllocWalk.cost310W cfg F size 1` (`970 + 320 · F` `regular_op_cost`s and the grow) above (through
`AllocWalk.f310_spec_walk`).

The chain above `f310_roomF` (`f770_spec`, `f767`, `f373`, `FmtGrow`, `FmtSink`, `FmtString`
(`costGrow`, `cost353`, `cost872`, `cost746`), `ToString.cost385`, `ToVec`, `SerdeLeaves`) states
its cost with `costAlloc` and its bound with `okF`; moving it to `okG` means replacing
`costAlloc cfg false size` by `costAllocF cfg F size` in those costs (`costAllocF_le2`: the same for
`F ≤ 2`, so the methods' gas bounds at `F ∈ {1, 2}` are unchanged).
-/

namespace WNear.Binary.VecWithCap

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocNewCell (cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (roomFor costAlloc)
open WNear.Binary.AllocZeroed (allocCode)

/-- The free-list bounds the general walk allocates on: any `F ≥ 1`. -/
def okG (F : Nat) : Prop := 1 ≤ F

theorem okG_of_okF {F : Nat} (h : okF F) : okG F := by
  unfold okG; rcases h with rfl | rfl <;> decide

/-- `__rust_alloc(size, 1)`'s cost on `heapInv … F`: `costAlloc` for `F ≤ 2`, the general walk's
`AllocWalk.cost310W` above. -/
def costAllocF (cfg : WasmConfig) (F : Nat) (size : UInt32) : Nat :=
  if F ≤ 2 then costAlloc cfg false size else AllocWalk.cost310W cfg F size 1

theorem costAllocF_le2 (cfg : WasmConfig) {F : Nat} (h : F ≤ 2) (size : UInt32) :
    costAllocF cfg F size = costAlloc cfg false size := by
  simp [costAllocF, h]

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `f310_roomF` for any `F ≥ 1`: a block, the bound `F` kept, at `costAllocF cfg F size`. -/
theorem f310_roomG (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8) (hsp : 16 ≤ sp.toNat)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4) (hr : roomFor len maxP size)
    (hF : okG F) :
    allocCode n maxP inst mi A ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
      A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => costAllocF cfg F size)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % (1 : UInt32).toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) 1).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) F ∗ block n p.toNat size.toNat)) := by
  unfold okG at hF
  by_cases h2 : F ≤ 2
  · rw [show (fun _ : List Value => costAllocF cfg F size) = (fun _ => 15 * cfg.regularOpCost +
        (15 * cfg.regularOpCost + (910 * cfg.regularOpCost + cfg.linearOpBaseCost +
          cfg.linearOpUnitCost * (cellPages (wordsOf size) 1).toNat))) from by
      funext _; rw [costAllocF_le2 cfg h2]; rfl]
    exact f310_roomF cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size idx maxP len live F o1 o2 o4 hsp
      hsize hsize2 ho1 ho2 ho4 hr (by unfold okF; omega)
  · obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr
    rw [show (fun _ : List Value => costAllocF cfg F size) = (fun _ => AllocWalk.cost310W cfg F size 1) from by
      funext _; simp [costAllocF, h2]]
    have hmx : max F 1 = F := Nat.max_eq_left hF
    iintro ⟨#Hc, #H236, #H581, #H575⟩
    iunfold allocCode at Hc
    icases Hc with ⟨#H0, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11⟩
    have key := AllocWalk.f310_spec_walk (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size 1 idx 0
      maxP len live F o1 o2 o4 hsp rfl (by decide) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax
    rw [hmx] at key
    iapply key
    iunfold AllocTwo.code310
    iframe H0 H236 H581 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H575 H11

end Spec

end WNear.Binary.VecWithCap
