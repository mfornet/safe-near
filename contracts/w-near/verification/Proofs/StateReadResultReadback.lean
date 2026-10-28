import NearVM.MemoryListWordRules
import Proofs.StateReadResultFrame
import Proofs.AllocateLayoutWrapperReadback

/-! Readback of the actual f498 low-eight-byte then high-four-byte copy. -/
namespace WNear.Proofs.StateReadResult
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 lowMemory finalMemory

/-- The final high write is adjacent to the low result, so the low snapshot survives. -/
theorem finalMemory_read_low (memory : Memory) (out source : UInt32) (hw : memory.wf)
    (hl : out.toNat+8≤memory.byteSize) (hh : (out+8).toNat+4≤memory.byteSize)
    (hn : (out+8).toNat=out.toNat+8) :
    readI64 (finalMemory memory out source) out.toNat=readI64 memory source.toNat := by
  have lo := writeI64_spec memory out.toNat (readI64 memory source.toNat) hw hl
  have hb : (out+8).toNat+4≤(lowMemory memory out source).byteSize := by
    rw [show (lowMemory memory out source).byteSize=memory.byteSize from by unfold lowMemory;exact lo.2.1];exact hh
  have lw : (lowMemory memory out source).wf := by unfold lowMemory;exact lo.1
  have hi := writeI32_spec (lowMemory memory out source) (out+8).toNat
    (readI32 (lowMemory memory out source) (source+8).toNat) lw hb
  apply StorePairReadback.readI64_of_bytes
  intro i hi8
  unfold finalMemory
  rw [hi.2.2.2,ite_eq_right (by rw [hn];omega)]
  unfold lowMemory
  rw [lo.2.2.2,ite_eq_left (by omega),Nat.add_sub_cancel_left]

/-- Recovering the original source high word needs precisely this write/read separation. -/
theorem finalMemory_read_high_original (memory : Memory) (out source : UInt32) (hw : memory.wf)
    (hl : out.toNat+8≤memory.byteSize) (hh : (out+8).toNat+4≤memory.byteSize)
    (hs : (source+8).toNat+4≤out.toNat ∨ out.toNat+8≤(source+8).toNat) :
    readI32 (finalMemory memory out source) (out+8).toNat=readI32 memory (source+8).toNat := by
  rw [finalMemory_read_high memory out source hw hl hh]
  have lo := writeI64_spec memory out.toNat (readI64 memory source.toNat) hw hl
  apply readI32_congr_bytes
  intro i hi
  unfold lowMemory
  rw [lo.2.2.2,ite_eq_right (by omega)]

theorem finalMemory_outside (memory : Memory) (out source : UInt32) (hw : memory.wf)
    (hl : out.toNat+8≤memory.byteSize) (hh : (out+8).toNat+4≤memory.byteSize)
    (hn : (out+8).toNat=out.toNat+8) (j : Nat) (hj : j<out.toNat ∨ out.toNat+12≤j) :
    (finalMemory memory out source).read8 j=memory.read8 j := by
  rw [(finalMemory_spec memory out source hw hl hh).2.2.2 j,
    ite_eq_right (by rw [hn];omega),ite_eq_right (by omega)]

private theorem word_of_packed_eq (first second : Memory) (out source offset : Nat)
    (ho : offset+4≤8) (heq : readI64 first out=readI64 second source) :
    readI32 first (out+offset)=readI32 second (source+offset) := by
  have bytes (i : Nat) (hi : i<4) : first.read8 (out+offset+i)=second.read8 (source+offset+i) := by
    have eq := congrArg (fun v : UInt64=>UInt8.ofNat (v.toNat >>> (8*(offset+i)))) heq
    rw [AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega),
      AllocateLayoutWrapperReadback.readI64_byte _ _ _ (by omega)] at eq
    simpa only [Nat.add_assoc] using eq
  have zero : first.read8 (out+offset)=second.read8 (source+offset) := by
    simpa only [Nat.add_zero] using bytes 0 (by decide)
  simp [readI32,List.range_succ,bytes,zero]

/-- Both low words copy the original packed snapshot without any source/output separation. -/
theorem finalMemory_low_words (memory : Memory) (out source : UInt32) (hw : memory.wf)
    (hl : out.toNat+8≤memory.byteSize) (hh : (out+8).toNat+4≤memory.byteSize)
    (hn : (out+8).toNat=out.toNat+8) :
    readI32 (finalMemory memory out source) out.toNat=readI32 memory source.toNat ∧
    readI32 (finalMemory memory out source) (out.toNat+4)=readI32 memory (source.toNat+4) := by
  have packed := finalMemory_read_low memory out source hw hl hh hn
  have lo := word_of_packed_eq (finalMemory memory out source) memory out.toNat source.toNat 0 (by decide) packed
  exact ⟨by simpa only [Nat.add_zero] using lo,
    word_of_packed_eq (finalMemory memory out source) memory out.toNat source.toNat 4 (by decide) packed⟩
end WNear.Proofs.StateReadResult
