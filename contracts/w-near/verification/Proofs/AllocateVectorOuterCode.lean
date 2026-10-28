import Proofs.AllocateVectorOuterState
import Proofs.AllocateVectorCode

/-! Actual installed descriptors for687 and its686 callee, all on the original store. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  vector : AllocateVector.Code s inst p.toVector
  index686 : p.mi.funcAddrs[686]?=some p.address686
  function686 : s.funcs[p.address686]?=some (.wasm WNear.Binary.AllocateVector.signature inst WNear.Binary.AllocateVector.function)

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  refine ⟨h.vector.transport s t inst p.toVector hf hm ht,h.index686,?_⟩
  rw [hf];exact h.function686

theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) :
    Code (paid s op n) inst p := by
  induction n with | zero=>exact h | succ n ih=>exact ih.transport _ _ inst p rfl rfl rfl
end WNear.Proofs.AllocateVectorOuter
