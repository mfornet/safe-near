import Proofs.InterfaceSetLazyReady
import Proofs.InterfaceLazyReadback

/-! Initial native span conditions for the lazy setter's computed heaps. -/
namespace WNear.Proofs.InterfaceSetLazyNative
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceSetState
open WNear.Proofs.InterfaceSetLazyState
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] readI32 writeI32

structure Native (p : Layout) : Prop where
  wf : p.memory.wf
  width : p.memory.byteSize ≤ 2 ^ 32
  outerSpan : (scratch p).toNat + 32 ≤ p.memory.byteSize
  innerSpan : (scratch p - 48).toNat + 48 ≤ p.memory.byteSize
  cellSpan : 1074900 + 16 ≤ p.memory.byteSize
  outerSeparated : (scratch p).toNat + 32 ≤ 1074900 ∨ 1074916 ≤ (scratch p).toNat
  innerSeparated : (scratch p - 48).toNat + 48 ≤ 1074900 ∨ 1074916 ≤ (scratch p - 48).toNat
  empty : readI32 p.memory 1074900 = 0
  aligned : ((scratch p + 24) ||| 4) = scratch p + 28

private theorem write_self (m : Memory) (address : Nat) (value : UInt32)
    (hw : m.wf) (hb : address + 4 ≤ m.byteSize) : readI32 (writeI32 m address value) address = value := by
  have hs := writeI32_spec m address value hw hb
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  rw [hs.2.2.2]
  have inside : address ≤ address + i ∧ address + i < address + 4 := by omega
  rw [ite_eq_left inside]
  simp only [Nat.add_sub_cancel_left]

private theorem write_frame (m : Memory) (address target : Nat) (value : UInt32)
    (hw : m.wf) (hb : address + 4 ≤ m.byteSize)
    (hsep : target + 4 ≤ address ∨ address + 4 ≤ target) :
    readI32 (writeI32 m address value) target = readI32 m target := by
  have hs := writeI32_spec m address value hw hb
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  rw [hs.2.2.2]
  have outside : ¬(address ≤ target + i ∧ target + i < address + 4) := by omega
  rw [ite_eq_right outside]

/-- Argument saving preserves the thread-local status before lazy lookup. -/
theorem saved_spec (p : Layout) (hr : Native p) :
    (savedMemory p).wf ∧ (savedMemory p).byteSize = p.memory.byteSize ∧
    (savedMemory p).max = p.memory.max ∧ readI32 (savedMemory p) 1074900 = 0 := by
  let s := (scratch p).toNat
  have b1 : s + 20 + 4 ≤ p.memory.byteSize := by have h := hr.outerSpan; dsimp [s]; omega
  have w1 := writeI32_spec p.memory (s + 20) p.vtable hr.wf b1
  have b2 : s + 16 + 4 ≤ (writeI32 p.memory (s + 20) p.vtable).byteSize := by rw [w1.2.1]; have h := hr.outerSpan; dsimp [s]; omega
  have w2 := writeI32_spec (writeI32 p.memory (s + 20) p.vtable) (s + 16) p.receiver w1.1 b2
  have r1 := write_frame p.memory (s + 20) 1074900 p.vtable hr.wf b1 (by have h := hr.outerSeparated; dsimp [s]; omega)
  have r2 := write_frame (writeI32 p.memory (s + 20) p.vtable) (s + 16) 1074900 p.receiver w1.1 b2
    (by have h := hr.outerSeparated; dsimp [s]; omega)
  exact ⟨w2.1, w2.2.1.trans w1.2.1, w2.2.2.1.trans w1.2.2.1, r2.trans (r1.trans hr.empty)⟩

/-- The complete lazy initializer's native obligations follow from initial spans. -/
theorem lazy_native (p : Layout) (initializerAddress : Nat) (hr : Native p) :
    InterfaceLazyNative.Native (lookupLayout p initializerAddress) := by
  have hs := saved_spec p hr
  refine ⟨hs.1, ?_, ?_, ?_, hr.innerSeparated, hs.2.2.2⟩
  · change (savedMemory p).byteSize ≤ 2 ^ 32
    rw [hs.2.1]; exact hr.width
  · change 1074900 + 16 ≤ (savedMemory p).byteSize
    rw [hs.2.1]; exact hr.cellSpan
  · change (scratch p - 48).toNat + 48 ≤ (savedMemory p).byteSize
    rw [hs.2.1]; exact hr.innerSpan

theorem lazy_bounds (p : Layout) (initializerAddress : Nat) (hr : Native p) :
    InterfaceLazyTail.Bounds (InterfaceLazyComplete.tailLayout (lookupLayout p initializerAddress)) :=
  InterfaceLazyNative.bounds (lookupLayout p initializerAddress) (lazy_native p initializerAddress hr)

theorem memory_spec (p : Layout) (initializerAddress : Nat) (hr : Native p) :
    (memory p initializerAddress).wf ∧ (memory p initializerAddress).byteSize = p.memory.byteSize ∧
    readI32 (memory p initializerAddress) 1074904 = 0 ∧ readI32 (memory p initializerAddress) 1074908 = 0 := by
  have hn := lazy_native p initializerAddress hr
  have spec := InterfaceLazyReadback.spec (lookupLayout p initializerAddress) hn
  have counter := InterfaceLazyReadback.counter_word (lookupLayout p initializerAddress) hn
  have receiver := InterfaceLazyReadback.receiver_word (lookupLayout p initializerAddress) hn
  exact ⟨spec.1, spec.2.1.trans (saved_spec p hr).2.1, counter, receiver⟩

end WNear.Proofs.InterfaceSetLazyNative
