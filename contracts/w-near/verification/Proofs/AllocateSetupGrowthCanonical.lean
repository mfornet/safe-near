import Proofs.AllocateSetupGrowth

/-! A deterministic pure-memory growth witness after stack setup. No future
primitive result or callee execution is assumed when constructing the layout. -/
namespace WNear.Proofs.AllocateSetupGrowth
open Wasm

def grownMemory (memory : Memory) (delta : Nat) : Memory :=
  {memory with pages:=memory.pages++Array.replicate delta ByteArray.empty}

theorem grow_eq_of_shape (source target originalGrown : Memory) (delta : Nat)
    (hsize : target.size=source.size) (hmax : target.max=source.max)
    (hgrow : source.grow delta=some originalGrown) :
    target.grow delta=some (grownMemory target delta) := by
  obtain ⟨grown,ht⟩ := grow_success_of_shape source target originalGrown delta hsize hmax hgrow
  unfold Memory.grow at ht ⊢
  dsimp only at ht ⊢
  split at ht
  · cases ht
  · split at ht <;> simp_all [grownMemory]

theorem grownMemory_spec_of_shape (source target originalGrown : Memory) (delta : Nat)
    (hsize : target.size=source.size) (hmax : target.max=source.max)
    (hgrow : source.grow delta=some originalGrown) (hwf : target.wf) :
    (grownMemory target delta).wf ∧
    (grownMemory target delta).byteSize=target.byteSize+delta*pageSize ∧
    (grownMemory target delta).max=target.max ∧
    (grownMemory target delta).size=target.size+delta ∧
    ∀ j, (grownMemory target delta).read8 j=if j<target.byteSize then target.read8 j else 0 :=
  Memory.grow_spec hwf (grow_eq_of_shape source target originalGrown delta hsize hmax hgrow)
end WNear.Proofs.AllocateSetupGrowth
