import Wasm.MemoryLemmas

/-! Stack setup writes may change bytes before allocation. Growth success is
transported from original capacity data, not assumed for a future callee. -/
namespace WNear.Proofs.AllocateSetupGrowth
open Wasm

/-- Memory growth checks only the page count and declared maximum. Exact
original success therefore derives success after shape-preserving setup writes. -/
theorem grow_success_of_shape (source target originalGrown : Memory) (delta : Nat)
    (hsize : target.size=source.size) (hmax : target.max=source.max)
    (hgrow : source.grow delta=some originalGrown) :
    ∃ grown, target.grow delta=some grown := by
  cases ht : target.grow delta with
  | some grown => exact ⟨grown,rfl⟩
  | none =>
    have failure := Memory.grow_none.mp ht
    rw [hsize,hmax] at failure
    have bad := Memory.grow_none.mpr failure
    rw [hgrow] at bad
    cases bad

/-- The derived primitive result provides all byte, size, limit and well-formed
memory facts required by the allocator's original growth contract. -/
theorem grow_spec_of_shape (source target originalGrown : Memory) (delta : Nat)
    (hsize : target.size=source.size) (hmax : target.max=source.max)
    (hgrow : source.grow delta=some originalGrown) (hwf : target.wf) :
    ∃ grown, target.grow delta=some grown ∧ grown.wf ∧
      grown.byteSize=target.byteSize+delta*pageSize ∧ grown.max=target.max ∧
      grown.size=target.size+delta ∧
      ∀ j, grown.read8 j=if j<target.byteSize then target.read8 j else 0 := by
  obtain ⟨grown,ht⟩ := grow_success_of_shape source target originalGrown delta hsize hmax hgrow
  exact ⟨grown,ht,Memory.grow_spec hwf ht⟩
end WNear.Proofs.AllocateSetupGrowth
