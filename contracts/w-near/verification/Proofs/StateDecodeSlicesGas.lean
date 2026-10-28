import Proofs.StateDecodeSlicesResult
import Proofs.AllocateSearchGasCost

/-! Exact typed slice-call accounting, independent of memory and control premises. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_charge)

theorem callAfter_units (drop : Bool) (s : Store NearState) (op index : Nat)
    (memory : Memory) (out pointer len split : UInt32) :
    GasUnits s (callAfter drop s op index memory out pointer len split) op
      (WNear.Binary.StateDecodeSlices.bodyCost drop+12) := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have entry : GasUnits s (entered s op) op 12 := first.trans (gasUnits_charge (chargedStore s op) op 11)
  have body : GasUnits (entered s op) (after drop (entered s op) op index memory out pointer len split)
      op (WNear.Binary.StateDecodeSlices.bodyCost drop) := by
    intro rest hc
    exact ⟨(after_gas drop (entered s op) op index rest memory out pointer len split hc).1,
      (after_gas drop (entered s op) op index rest memory out pointer len split hc).2,
      after_credits drop (entered s op) op index rest memory out pointer len split hc⟩
  simpa only [callAfter,Nat.add_comm] using entry.trans body
end WNear.Proofs.StateDecodeSlices
