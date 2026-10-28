import Proofs.StateDecodeRawRecordState

/-! Code installation is transported by arrays, without unfolding any computed heap. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic

theorem RecordCode.transport (s t : Store NearState) (inst : Nat) (q : AllocatePositive.Layout)
    (a581 a236 a310 : Nat) (h : RecordCode s inst q a581 a236 a310)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    RecordCode t inst q a581 a236 a310 := by
  refine {h with allocation:=h.allocation.transport s t inst q hf hm ht,function581:=?_,function236:=?_,function310:=?_}
  · rw[hf];exact h.function581
  · rw[hf];exact h.function236
  · rw[hf];exact h.function310
end WNear.Proofs.StateDecodeRaw
