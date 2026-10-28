import Proofs.StateReadStorageOuterBorrow
import Proofs.StateReadStorageOuterMemory

/-! Complete459 memory extent and old static-word frames follow from the original
548 setup; its canonical host leaves guest memory untouched. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 setupMemory storageMemory

theorem storageMemory_footprint (p : Layout) (hn : Native p) :
    (storageMemory p).wf ∧ (storageMemory p).byteSize=p.memory.byteSize ∧ (storageMemory p).max=p.memory.max ∧
    ∀ j, p.sp548.toNat≤j → (j<1074904 ∨ 1074908≤j) → (storageMemory p).read8 j=p.memory.read8 j := by
  have setup := setup_spec p hn
  have bounds := setup_native_bounds p hn
  have counter := counter_eq p hn
  have final := StateDispatchLength.finalMemory_footprint (storageLayout p) setup.1 bounds.2 bounds.1
    (by rw [counter];exact bounds.2)
  have num := stack_numbers p hn
  have low := hn.spLower
  have sc : (StateDispatchLength.scratch (storageLayout p)).toNat=p.sp548.toNat-48 := num.2.1
  have finalWf : (storageMemory p).wf := by unfold storageMemory;exact final.1
  have finalSize : (storageMemory p).byteSize=p.memory.byteSize := by
    unfold storageMemory
    exact final.2.1.trans setup.2.1
  have finalMax : (storageMemory p).max=p.memory.max := by
    unfold storageMemory
    exact final.2.2.1.trans setup.2.2
  refine ⟨finalWf,finalSize,finalMax,?_⟩
  intro j hj hcell
  have step := final.2.2.2 j (Or.inr (by rw [sc];omega)) hcell (by rw [counter];exact hcell)
  unfold storageMemory
  rw [step]
  exact setup_byte p hn j hj

theorem storageMemory_size (p : Layout) (hn : Native p) : (storageMemory p).size=p.memory.size := by
  have h := (storageMemory_footprint p hn).2.1
  change (storageMemory p).size*65536=p.memory.size*65536 at h
  omega

theorem storageMemory_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.sp548.toNat≤address) (hc : address+4≤1074904 ∨ 1074908≤address) :
    readI32 (storageMemory p) address=readI32 p.memory address := by
  apply readI32_congr_bytes
  intro i hi
  exact (storageMemory_footprint p hn).2.2.2 (address+i) (by omega) (by omega)
end WNear.Proofs.StateReadStorageOuter
