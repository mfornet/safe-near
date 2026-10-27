import NearVM.MeteredI32MemoryRules

/-! Native interval facts for the end-split branch of f580. All quantities are
computed from the original free-block header and requested word count. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic

def endWord (memory : Memory) (head : UInt32) : UInt32 := readI32 memory head.toNat &&& 4294967292
def splitPointer (memory : Memory) (head words : UInt32) := endWord memory head - words * 4
def splitHeader (memory : Memory) (head words : UInt32) := splitPointer memory head words - 8

/-- This is the large-enough original free-block condition, rather than a
post-allocation pointer or an execution-outcome assumption. -/
structure SplitNative (memory : Memory) (head words : UInt32) : Prop where
  wordsPositive : 0 < words.toNat
  room : head.toNat + 80 + words.toNat * 4 ≤ (endWord memory head).toNat
  endBound : (endWord memory head).toNat ≤ memory.byteSize

theorem split_pointer_toNat (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    (splitPointer memory head words).toNat = (endWord memory head).toNat - words.toNat * 4 := by
  have room := h.room
  have he := UInt32.toNat_lt (endWord memory head)
  have hw : words.toNat * 4 < 2^32 := by omega
  have count : (words*4).toNat = words.toNat*4 := by
    rw [UInt32.toNat_mul]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt hw
  unfold splitPointer
  rw [UInt32.toNat_sub,count]
  omega

theorem split_header_toNat (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    (splitHeader memory head words).toNat = (splitPointer memory head words).toNat - 8 := by
  have room := h.room
  have hp := split_pointer_toNat memory head words h
  have ht := UInt32.toNat_lt (splitPointer memory head words)
  unfold splitHeader
  rw [UInt32.toNat_sub]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

/-- The actual pointer header+8 is nonzero and its entire requested payload is
in memory; both facts follow from the original header and word count. -/
theorem split_result (memory : Memory) (head words : UInt32) (h : SplitNative memory head words) :
    splitHeader memory head words + 8 = splitPointer memory head words ∧
    splitPointer memory head words ≠ 0 ∧
    (splitPointer memory head words).toNat + words.toNat*4 ≤ memory.byteSize ∧
    (splitHeader memory head words).toNat + 12 ≤ memory.byteSize := by
  have hp := split_pointer_toNat memory head words h
  have hh := split_header_toNat memory head words h
  have hn : splitPointer memory head words ≠ 0 := by
    intro hz
    have hz' := congrArg UInt32.toNat hz
    simp only [UInt32.toNat_ofNat] at hz'
    have room := h.room
    omega
  refine ⟨UInt32.sub_add_cancel _ 8,hn,?_,?_⟩
  · have room := h.room
    have bound := h.endBound
    omega
  · have room := h.room
    have bound := h.endBound
    have positive := h.wordsPositive
    omega
end WNear.Proofs.Allocate
