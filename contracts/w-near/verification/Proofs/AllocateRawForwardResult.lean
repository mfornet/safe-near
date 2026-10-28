import Proofs.AllocateRawForwardOuterCall
import Proofs.AllocateRetryPayload

/-! Original-data payload and exact numeric costs for the actual raw forwarding calls. -/
namespace WNear.Proofs.AllocateRawForward
open Wasm Wasm.Near MeteredLogic

theorem costs (p : Layout) : cost236 p=606 ∧ steps236 p=494 ∧ cost310 p=621 ∧ steps310 p=501 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem payload (p : Layout) (hn : Native p) :
    AllocateRetry.result p≠0 ∧ (AllocateRetry.finalMemory p).wf ∧
    (AllocateRetry.finalMemory p).byteSize=p.memory.byteSize+(AllocateGrowth.delta (AllocateRetry.growthLayout p)).toNat*65536 ∧
    (AllocateRetry.finalMemory p).max=p.memory.max ∧
    (AllocateRetry.result p).toNat+p.size.toNat≤(AllocateRetry.finalMemory p).byteSize ∧
    (AllocateRetry.result p).toNat+p.size.toNat≤2^32 := by
  have shape := AllocateRetry.finalMemory_spec p hn
  exact ⟨(AllocateRetry.result_nonzero_and_span p hn).1,shape.1,shape.2.1,shape.2.2,
    AllocateRetry.result_size_span p hn,AllocateRetry.result_width p hn⟩

theorem callAfter310_result (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter310 cfg s p).mems[p.memoryIndex]?=some (AllocateRetry.finalMemory p) ∧
    AllocateRetry.result p≠0 ∧ (AllocateRetry.finalMemory p).wf ∧
    (AllocateRetry.result p).toNat+p.size.toNat≤(AllocateRetry.finalMemory p).byteSize ∧
    (AllocateRetry.result p).toNat+p.size.toNat≤2^32 := by
  have h := payload p hn
  exact ⟨callAfter310_memory cfg s p hm,h.1,h.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
end WNear.Proofs.AllocateRawForward
