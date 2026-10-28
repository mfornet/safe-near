import Proofs.StateDecodeScalarFinalMemory
import Proofs.StateDecodeScalarReadback
import Proofs.ValueReturnOuterLayout

/-! The updated caller slice is decoded from the cached original split descriptor. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 updatedMemory finalMemory

theorem updatedMemory_slice_words (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI32 (updatedMemory wide p) p.slice.toNat=p.pointer+width wide ∧
    readI32 (updatedMemory wide p) (p.slice.toNat+4)=p.length-width wide := by
  have shape:=valuesMemory_spec wide p hn
  have copy:=writeI64_spec (valuesMemory wide p) p.slice.toNat (dropValue wide p) shape.1
    (by rw [shape.2.1];exact hn.sliceBound)
  constructor
  · apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    unfold updatedMemory
    rw [copy.2.2.2,ite_eq_left (by omega),Nat.add_sub_cancel_left,dropValue_bytes wide p hn i (by omega)]
    exact ite_eq_left hi
  · apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    unfold updatedMemory
    rw [copy.2.2.2,ite_eq_left (by omega)]
    have offset : p.slice.toNat+4+i-p.slice.toNat=4+i := by omega
    rw [offset,dropValue_bytes wide p hn (4+i) (by omega),ite_eq_right (by omega)]
    congr 3
    omega

theorem finalMemory_slice_words (wide : Bool) (p : Layout) (hn : Native wide p)
    (hs : p.out.toNat+4≤p.slice.toNat ∨ p.slice.toNat+8≤p.out.toNat) :
    readI32 (finalMemory wide p) p.slice.toNat=p.pointer+width wide ∧
    readI32 (finalMemory wide p) (p.slice.toNat+4)=p.length-width wide := by
  have shape:=updatedMemory_spec wide p hn
  have hb : p.out.toNat+4≤(updatedMemory wide p).byteSize := by
    rw [shape.2.1]
    have h:=hn.outBound
    cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at h <;> omega
  have low:=PanicAllocateReadback.read_write_frame (updatedMemory wide p) p.slice.toNat p.out.toNat 0 shape.1 hb (by omega)
  have high:=PanicAllocateReadback.read_write_frame (updatedMemory wide p) (p.slice.toNat+4) p.out.toNat 0 shape.1 hb (by omega)
  have words:=updatedMemory_slice_words wide p hn
  unfold finalMemory
  exact ⟨low.trans words.1,high.trans words.2⟩
end WNear.Proofs.StateDecodeScalar
