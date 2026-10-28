import Proofs.AllocateRawForwardDirectOuterCall
import Proofs.AllocatePositivePayload

/-! Original-data payload and exact numeric costs for the actual raw forwarding calls. -/
namespace WNear.Proofs.AllocateRawForwardDirect
open Wasm Wasm.Near MeteredLogic

theorem costs (p : Layout) : cost236 p=361 ∧ steps236 p=302 ∧ cost310 p=376 ∧ steps310 p=309 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem payload (p : Layout) (hn : Native p) :
    AllocatePositive.result p≠0 ∧ (AllocatePositive.finalMemory p).wf ∧
    (AllocatePositive.finalMemory p).byteSize=p.memory.byteSize ∧
    (AllocatePositive.finalMemory p).max=p.memory.max ∧
    (AllocatePositive.result p).toNat+p.size.toNat≤(AllocatePositive.finalMemory p).byteSize ∧
    (AllocatePositive.result p).toNat+p.size.toNat≤2^32 := by
  have shape := AllocatePositive.finalMemory_spec p hn
  exact ⟨(AllocatePositive.result_nonzero_and_span p hn).1,shape.1,shape.2.1,shape.2.2,
    AllocatePositive.result_size_span p hn,AllocatePositive.result_width p hn⟩

theorem callAfter310_result (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hn : Native p) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter310 cfg s p).mems[p.memoryIndex]?=some (AllocatePositive.finalMemory p) ∧
    AllocatePositive.result p≠0 ∧ (AllocatePositive.finalMemory p).wf ∧
    (AllocatePositive.result p).toNat+p.size.toNat≤(AllocatePositive.finalMemory p).byteSize ∧
    (AllocatePositive.result p).toNat+p.size.toNat≤2^32 := by
  have h := payload p hn
  exact ⟨callAfter310_memory cfg s p hm,h.1,h.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
end WNear.Proofs.AllocateRawForwardDirect
