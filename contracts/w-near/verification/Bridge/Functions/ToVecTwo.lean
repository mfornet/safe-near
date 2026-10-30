import Bridge.Functions.FtTotalSupply

/-!
# `to_vec` (96) on the heap `state_read` leaves: `ToVecAfterFree … 0`

`toVecAfterFree_zero` discharges `FtTotalSupply.ToVecAfterFree cfg lim 0`: `ToVec.f96_spec` at the
free-list bound `F = 2` (the allocations go through `AllocTwo.f310_spec_two`, at the cost of
`AllocSeq.f310_spec_room`: no extra cost, `x96 = 0`). The heap after it is `heapInv … 3`
(`to_string`'s buffer freed onto a list of at most two cells).
-/

namespace WNear.Binary.ToVecTwo

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

/-- **`to_vec::<U128>` from `heapInv … 2`**, at no extra cost. -/
theorem toVecAfterFree_zero (cfg : WasmConfig) (lim : ExecLimits) : FtTotalSupply.ToVecAfterFree cfg lim 0 := by
  intro GF _ d type htype inst mi A n g ta hm hd Cg gt s out v ptr0 aidx ob maxP hl live lo hi hs hob hout hv
    hr1 hr2
  refine (ToVec.f96_spec cfg lim d type htype inst mi A n g ta hm hd Cg gt s out v ptr0 aidx ob maxP hl live
    lo hi hs hob hout hv hr1 hr2 (F := 2) (hF := by decide)).trans ?_
  refine (MFunSpec_cost (fun _ => (ToVec.cost96F_le2 cfg (by decide) lo hi).le.trans (Nat.le_add_right _ 0))).trans ?_
  refine MFunSpec_frame iprop(emp) (fun args => ?_) (fun args rs => ?_)
  · iintro H
    iframe H
  · iintro ⟨-, %hrs, Hg, Hs, Hv, HD, Hvt, %q, %rest, %hrest, O0, O4, O8, O12, Hq, %hl', Hh⟩
    iframe Hg Hs Hv HD Hvt
    isplitr; · ipureintro; exact hrs
    iexists q, rest
    iframe O0 O4 O8 O12 Hq
    isplitr; · ipureintro; exact hrest
    iexists hl', 2 + 1
    iexact Hh

end WNear.Binary.ToVecTwo
