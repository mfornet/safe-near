import Proofs.AllocateFlaggedMemory

/-! Bounds of the actual flags-two allocation result, derived from original heap data. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout)

theorem pointer_nonzero_and_span (p : Layout) (hn : Native p) :
    pointer p≠0 ∧ (pointer p).toNat+p.words.toNat*4≤(finalMemory p).byteSize := by
  have result := Allocate.split_result p.memory (head p) p.words hn.split
  have shape := final_shape p hn
  exact ⟨result.2.1,by rw [shape.size];exact result.2.2.1⟩

/-- A payload bounded by the requested word count fits the memory after the
actual sequential split; no post-allocation lookup supplies this fact. -/
theorem payload_span (p : Layout) (hn : Native p) (bytes : Nat)
    (hbytes : bytes≤p.words.toNat*4) :
    (pointer p).toNat+bytes≤(finalMemory p).byteSize := by
  have span := (pointer_nonzero_and_span p hn).2
  omega

theorem payload_width (p : Layout) (hn : Native p) (bytes : Nat)
    (hbytes : bytes≤p.words.toNat*4) (hw : p.memory.byteSize≤2^32) :
    (pointer p).toNat+bytes≤2^32 := by
  have span := payload_span p hn bytes hbytes
  rw [(final_shape p hn).size] at span
  exact span.trans hw
end WNear.Proofs.AllocateFlagged
