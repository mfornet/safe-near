import Proofs.StateDecodeRawFrame
import Proofs.StateDecodeRawGas
import Proofs.StateDecodeRawHost

/-! Exact selected f767 caller endpoints, including unconditional cached record
readback even when the caller output aliases earlier records or heap data. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] callAfterRaw enteredRaw afterRaw finalMemory

theorem callAfterRaw_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfterRaw cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  have initial : (enteredRaw s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory := by unfold enteredRaw;exact hm
  unfold callAfterRaw
  exact afterRaw_memory cfg (enteredRaw s cfg.regularOpCost) p hn initial

theorem callAfterRaw_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfterRaw cfg s p).funcs=s.funcs ∧ (callAfterRaw cfg s p).modules=s.modules ∧ (callAfterRaw cfg s p).tables=s.tables := by
  unfold callAfterRaw
  simpa only [enteredRaw,chargedStore] using afterRaw_fields cfg (enteredRaw s cfg.regularOpCost) p

theorem callAfterRaw_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.globalRaw) (hv : p.globalRaw.value=.i32 p.spRaw) :
    (callAfterRaw cfg s p).globals=s.globals := by
  have initial : (enteredRaw s cfg.regularOpCost).globals[p.globalIndex]?=some p.globalRaw := by unfold enteredRaw;exact hg
  unfold callAfterRaw
  simpa only [enteredRaw,chargedStore] using afterRaw_globals cfg (enteredRaw s cfg.regularOpCost) p hn initial hv

theorem callAfterRaw_record (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfterRaw cfg s p).mems[p.memoryIndex]?=some (finalMemory p) ∧
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧ (finalMemory p).max=p.memory.max ∧
    readI32 (finalMemory p) p.outRaw.toNat=result p ∧ readI32 (finalMemory p) (p.outRaw.toNat+4)=p.size := by
  have m:=finalMemory_spec p hn
  exact ⟨callAfterRaw_memory cfg s p hn hm,m.1,m.2.1,m.2.2.1,m.2.2.2.1,m.2.2.2.2.1⟩

theorem callAfterRaw_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (585*cfg.regularOpCost+rest)) :
    (callAfterRaw cfg s p).host.gas.Credits rest := (callAfterRaw_gas cfg s p rest hc).2.2
end WNear.Proofs.StateDecodeRaw
