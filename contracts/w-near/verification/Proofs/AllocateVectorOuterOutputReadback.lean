import Proofs.AllocateVectorOuterOutputFrame
import Proofs.AllocateLayoutWrapperReadback

/-! The eight-byte snapshot is captured before either output store, so even
an overlapping length store cannot change the returned pointer/size words. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 outputMemory

theorem outputMemory_word_of_snapshot (memory : Memory) (out count : UInt32)
    (source offset : Nat) (hw : memory.wf) (hb : out.toNat+12≤memory.byteSize)
    (ho : offset+4≤8) :
    readI32 (outputMemory memory out count (readI64 memory source)) (out.toNat+offset)=
      readI32 memory (source+offset) := by
  let high := writeI32 memory (out.toNat+8) count
  have a := writeI32_spec memory (out.toNat+8) count hw (by omega)
  have bnd : out.toNat+8≤high.byteSize := by rw [show high.byteSize=memory.byteSize from a.2.1];omega
  have b := writeI64_spec high out.toNat (readI64 memory source) a.1 bnd
  have bytes (i : Nat) (hi : i<4) :
      (outputMemory memory out count (readI64 memory source)).read8 (out.toNat+offset+i)=
        memory.read8 (source+offset+i) := by
    rw [outputMemory]
    change (writeI64 high out.toNat (readI64 memory source)).read8 (out.toNat+offset+i)=_
    rw [b.2.2.2,ite_eq_left (show out.toNat≤out.toNat+offset+i ∧ out.toNat+offset+i<out.toNat+8 by omega)]
    have idx : out.toNat+offset+i-out.toNat=offset+i := by omega
    rw [idx,AllocateLayoutWrapperReadback.readI64_byte memory source (offset+i) (by omega)]
    congr 1
    omega
  have zero : (outputMemory memory out count (readI64 memory source)).read8 (out.toNat+offset)=
      memory.read8 (source+offset) := by simpa only [Nat.add_zero] using bytes 0 (by decide)
  simp [readI32,List.range_succ,bytes,zero]

 theorem outputMemory_words_of_snapshot (memory : Memory) (out count : UInt32) (source : Nat)
    (hw : memory.wf) (hb : out.toNat+12≤memory.byteSize) :
    readI32 (outputMemory memory out count (readI64 memory source)) out.toNat=readI32 memory source ∧
    readI32 (outputMemory memory out count (readI64 memory source)) (out.toNat+4)=readI32 memory (source+4) := by
  have low := outputMemory_word_of_snapshot memory out count source 0 hw hb (by decide)
  have high := outputMemory_word_of_snapshot memory out count source 4 hw hb (by decide)
  exact ⟨by simpa only [Nat.add_zero] using low,high⟩
end WNear.Proofs.AllocateVectorOuter
