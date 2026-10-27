import Proofs.UnwrapStateCallees
import Proofs.UnwrapStateCopyEffects

/-! Functional model-data effects of the complete accepted f155 call. -/
namespace WNear.Proofs.UnwrapStateEffects
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply
attribute [local irreducible] UnwrapStateCopyEntry.callAfter ForwardCopyMemory.forward

/-- The complete local call installs the actual sequential forty-byte copy. -/
theorem callAfter_memory (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + 40 ≤ memory.byteSize) (hwrite : out.toNat + 40 ≤ memory.byteSize) :
    (UnwrapStateCallees.callAfter s op index out source memory).mems[index]? =
      some (ForwardCopyMemory.forward memory out.toNat source.toNat 40) := by
  have hm : (UnwrapState.argumentStore (UnwrapStateCallees.entered s op) op).mems[index]? = some memory := by
    simpa only [UnwrapState.argumentStore, UnwrapStateCallees.entered, StorePairCaller.paid, chargedStore] using hmemory
  have h := UnwrapStateCopyEffects.callAfter_memory
    (UnwrapState.argumentStore (UnwrapStateCallees.entered s op) op) op index out source memory 40 hm hwf hwidth hread hwrite
  exact h

/-- The wrapper's actual stack-relative regions are disjoint even when the
pointer additions wrap. Native execution bounds are checked separately. -/
theorem getter_disjoint (scratch : UInt32) :
    (scratch + 32).toNat + 40 ≤ (scratch + 72).toNat ∨
      (scratch + 72).toNat + 40 ≤ (scratch + 32).toNat := by
  have hs := scratch.toNat_lt
  rw [UInt32.toNat_add, UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- Original decoded U128 data reaches the unwrapped object through the real
byte loop. No post-call representation or copy-execution premise is needed. -/
theorem callAfter_u128 (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (value : Nat) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + 40 ≤ memory.byteSize) (hwrite : out.toNat + 40 ≤ memory.byteSize)
    (hdisjoint : out.toNat + 40 ≤ source.toNat ∨ source.toNat + 40 ≤ out.toNat)
    (hv : U128At memory source.toNat value) :
    ∃ result, (UnwrapStateCallees.callAfter s op index out source memory).mems[index]? = some result ∧
      U128At result out.toNat value := by
  let result := ForwardCopyMemory.forward memory out.toNat source.toNat 40
  have hlo := ForwardCopyMemory.copied_word memory out.toNat source.toNat 40 0 hwf hwrite hdisjoint (by omega)
  have hhi := ForwardCopyMemory.copied_word memory out.toNat source.toNat 40 8 hwf hwrite hdisjoint (by omega)
  simp only [Nat.add_zero] at hlo
  refine ⟨result, callAfter_memory s op index out source memory hmemory hwf hwidth hread hwrite, ?_⟩
  change (readI64 result out.toNat).toNat + 2 ^ 64 * (readI64 result (out.toNat + 8)).toNat = value
  rw [hlo, hhi]
  exact hv

end WNear.Proofs.UnwrapStateEffects
