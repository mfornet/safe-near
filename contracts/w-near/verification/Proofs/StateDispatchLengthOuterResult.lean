import Proofs.StateDispatchLengthOuterNative
import Proofs.StateDispatchLengthOuterBody
import Proofs.StateDispatchLengthOuterTailFrame

/-! The actual option stores return the original register's length when the
original stack and counter spans keep its input word intact. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 readI64 writeI64
set_option maxRecDepth 16384

def resultMemory (s : Store NearState) (p : Layout) :=
  StateDispatchLengthOuterTail.finalMemory (StateDispatchLength.finalMemory p.inner) p.out (resultValue s p)

theorem resultValue_eq (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (hr : Ready s limits frame callers p extra)
    (hstack : 32 ≤ p.sp.toNat)
    (hcounter : p.sp.toNat ≤ 1074904 ∨ 1074916 ≤ p.sp.toNat) :
    resultValue s p = StateReadRegister.lengthValue s p.register := by
  unfold resultValue
  rw [register_readback s limits frame callers p extra hr hstack hcounter]

theorem Ready.resultMemory_specs (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hr : Ready s limits frame callers p extra) :
    (resultMemory s p).wf ∧ (resultMemory s p).byteSize = p.memory.byteSize ∧
    (resultMemory s p).max = p.memory.max ∧
    readI64 (resultMemory s p) p.out.toNat = StateDispatchLengthOuterTail.present (resultValue s p) ∧
    readI64 (resultMemory s p) (p.out.toNat+8) = resultValue s p := by
  have inner := (hr.callee cfg s limits frame callers p extra 0 []).finalMemory_specs _ _ _ _ _ _
  have written := writeI64_spec p.memory ((scratch p).toNat+8) p.register hr.memoryWf
    (by have := hr.inputWriteBound; omega)
  have size : p.inner.memory.byteSize = p.memory.byteSize := by
    rw [hr.native.memory_eq]
    exact written.2.1
  have maximum : p.inner.memory.max = p.memory.max := by
    rw [hr.native.memory_eq]
    exact written.2.2.1
  have outputBound : p.out.toNat+16 ≤ (StateDispatchLength.finalMemory p.inner).byteSize := by
    rw [inner.2.1,size]
    exact hr.outBound
  have output := StateDispatchLengthOuterTail.finalMemory_spec (StateDispatchLength.finalMemory p.inner)
    p.out (resultValue s p) inner.1 outputBound
  exact ⟨output.1,output.2.1.trans (inner.2.1.trans size),
    output.2.2.1.trans (inner.2.2.trans maximum),output.2.2.2.1,output.2.2.2.2.1⟩

theorem finalStore_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hi : p.inner.mi.memAddrs[0]? = some p.inner.memoryIndex)
    (hm : s.mems[p.inner.memoryIndex]? = some p.memory) (hn : Native p) :
    (finalStore cfg s p).mems[p.inner.memoryIndex]? = some (resultMemory s p) := by
  have args := arguments_memory s cfg.regularOpCost p hm hn
  have lookedMemory := StateDispatchLength.callAfter_memory cfg (arguments s cfg.regularOpCost p) p.inner hi args
  exact StateDispatchLengthOuterTail.after_memory (looked cfg s p) cfg.regularOpCost
    p.inner.memoryIndex p.inner.globalIndex (StateDispatchLength.finalMemory p.inner)
    p.out (scratch p) (resultValue s p) lookedMemory

end WNear.Proofs.StateDispatchLengthOuter
