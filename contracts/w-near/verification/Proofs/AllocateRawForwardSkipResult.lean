import Proofs.AllocateRawForwardSkipOuterCall
import Proofs.AllocatePositiveSkipPayload

/-! Original-data payload and exact numeric costs for the actual raw forwarding calls. -/
namespace WNear.Proofs.AllocateRawForwardSkip
open Wasm Wasm.Near MeteredLogic

theorem costs (p : Layout) : cost236 p=432 ∧ steps236 p=361 ∧ cost310 p=447 ∧ steps310 p=368 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem payload (p : Layout) (hn : Native p) :
    AllocatePositiveSkip.result p≠0 ∧ (AllocatePositiveSkip.finalMemory p).wf ∧
    (AllocatePositiveSkip.finalMemory p).byteSize=p.memory.byteSize ∧
    (AllocatePositiveSkip.finalMemory p).max=p.memory.max ∧
    (AllocatePositiveSkip.result p).toNat+p.size.toNat≤(AllocatePositiveSkip.finalMemory p).byteSize ∧
    (AllocatePositiveSkip.result p).toNat+p.size.toNat≤2^32 := by
  have shape := AllocatePositiveSkip.finalMemory_spec p hn
  exact ⟨(AllocatePositiveSkip.result_nonzero_and_span p hn).1,shape.1,shape.2.1,shape.2.2,
    AllocatePositiveSkip.result_size_span p hn,AllocatePositiveSkip.result_width p hn⟩

theorem callAfter310_result (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter310 cfg s p).mems[p.memoryIndex]?=some (AllocatePositiveSkip.finalMemory p) ∧
    AllocatePositiveSkip.result p≠0 ∧ (AllocatePositiveSkip.finalMemory p).wf ∧
    (AllocatePositiveSkip.result p).toNat+p.size.toNat≤(AllocatePositiveSkip.finalMemory p).byteSize ∧
    (AllocatePositiveSkip.result p).toNat+p.size.toNat≤2^32 := by
  have h := payload p hn
  exact ⟨callAfter310_memory cfg s p hm,h.1,h.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
end WNear.Proofs.AllocateRawForwardSkip
