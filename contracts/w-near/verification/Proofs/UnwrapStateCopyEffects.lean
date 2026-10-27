import Proofs.UnwrapStateCopyEntry
import Proofs.UnwrapStateCopyMemory
import Proofs.UnwrapStateCopyGas

/-! Functional effects of the actual returning f951 call. -/
namespace WNear.Proofs.UnwrapStateCopyEffects
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.UnwrapStateCopyEntry

/-- Caller instruction, activation, setup and final get/return leave the loop's
concrete sequential memory intact. -/
theorem callAfter_memory (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize) :
    (callAfter s op index out source memory count).mems[index]? =
      some (ForwardCopyMemory.forward memory out.toNat source.toNat count) := by
  have hm : (prepared (calledStore s op) op).mems[index]? = some memory := by
    simpa only [prepared, calledStore, StorePairCaller.paid, chargedStore] using hmemory
  exact UnwrapStateCopyMemory.loopStore_memory (prepared (calledStore s op) op) op index out source memory count
    hm hwf hwidth hread hwrite

/-- The complete local call preserves all other Wasm resources. -/
theorem callAfter_resources (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) :
    {callAfter s op index out source memory count with mems := s.mems, host := s.host} = s := by
  have h := UnwrapStateCopyMemory.loopStore_frame (prepared (calledStore s op) op) op index out source memory count
  have hr := congrArg (fun store : Store NearState => {store with mems := s.mems, host := s.host}) h
  simpa only [callAfter, finalStore, prepared, calledStore, StorePairCaller.paid, chargedStore] using hr

/-- Persistent storage, registers and functional host data survive the call. -/
theorem callAfter_host_frame (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) :
    {(callAfter s op index out source memory count).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  have h := UnwrapStateCopyMemory.loopStore_host_frame (prepared (calledStore s op) op) op index out source memory count
  have hr := congrArg (fun host : NearState => {host with gas := s.host.gas, gasProfile := s.host.gasProfile}) h
  simpa only [callAfter, finalStore, prepared, calledStore, StorePairCaller.paid, chargedStore, chargeHost] using hr

/-- At disjoint call sites, every complete copied word has its original value. -/
theorem callAfter_word (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count offset : Nat) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize)
    (hdisjoint : out.toNat + count ≤ source.toNat ∨ source.toNat + count ≤ out.toNat)
    (hoffset : offset + 8 ≤ count) :
    ∃ result, (callAfter s op index out source memory count).mems[index]? = some result ∧
      readI64 result (out.toNat + offset) = readI64 memory (source.toNat + offset) :=
  ⟨_, callAfter_memory s op index out source memory count hmemory hwf hwidth hread hwrite,
    ForwardCopyMemory.copied_word memory out.toNat source.toNat count offset hwf hwrite hdisjoint hoffset⟩

end WNear.Proofs.UnwrapStateCopyEffects
