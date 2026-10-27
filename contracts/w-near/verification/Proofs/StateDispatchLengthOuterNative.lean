import Proofs.StateDispatchLengthOuterState
import Proofs.StateDispatchLengthInputFrame
import Proofs.StorePairReadback
import Proofs.StorePairAddresses

/-! Original stack and counter separation derive f524's register-id readback. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 readI64 writeI64
set_option maxRecDepth 16384

theorem register_readback (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (hr : Ready s limits frame callers p extra)
    (hstack : 32 ≤ p.sp.toNat)
    (hcounter : p.sp.toNat ≤ 1074904 ∨ 1074916 ≤ p.sp.toNat) :
    StateDispatchLength.register p.inner = p.register := by
  have h16 : 16 ≤ p.sp.toNat := by omega
  have outNat : (scratch p).toNat = p.sp.toNat - 16 := StorePairAddresses.sub_sixteen p.sp h16
  have inputNat : p.inner.input.toNat = (scratch p).toNat + 8 := by
    rw [hr.native.input_eq]
    exact StorePairAddresses.scratch_add_eight p.sp h16
  have innerScratchNat : (StateDispatchLength.scratch p.inner).toNat = p.sp.toNat - 32 := by
    have hs : 16 ≤ (scratch p).toNat := by rw [outNat]; omega
    change (p.inner.sp - 16).toNat = p.sp.toNat - 32
    rw [hr.native.sp_eq,StorePairAddresses.sub_sixteen (scratch p) hs,outNat]
    omega
  have endInput : (scratch p).toNat + 8 + 8 ≤ p.memory.byteSize := by have h := hr.inputWriteBound; omega
  have stackBound : (StateDispatchLength.scratch p.inner).toNat + 16 ≤ p.memory.byteSize := by
    rw [innerScratchNat]
    rw [outNat] at endInput
    omega
  have cs : p.inner.input.toNat + 8 ≤ 1074904 ∨ 1074908 ≤ p.inner.input.toNat := by
    rw [inputNat,outNat]
    rcases hcounter with h | h <;> omega
  have ss : p.inner.input.toNat + 8 ≤ (StateDispatchLength.scratch p.inner).toNat ∨
      (StateDispatchLength.scratch p.inner).toNat + 16 ≤ p.inner.input.toNat := by
    rw [inputNat,outNat,innerScratchNat]
    omega
  have write := writeI64_spec p.memory ((scratch p).toNat + 8) p.register hr.memoryWf endInput
  have innerWf : p.inner.memory.wf := by rw [hr.native.memory_eq]; exact write.1
  have innerSize : p.inner.memory.byteSize = p.memory.byteSize := by rw [hr.native.memory_eq]; exact write.2.1
  have bytesRead : readI64 (inputMemory p) ((scratch p).toNat + 8) = p.register := by
    apply StorePairReadback.readI64_of_bytes
    intro i hi
    have span : (scratch p).toNat + 8 ≤ (scratch p).toNat + 8 + i ∧
        (scratch p).toNat + 8 + i < (scratch p).toNat + 8 + 8 := by omega
    rw [show (inputMemory p).read8 ((scratch p).toNat + 8 + i) = _ from write.2.2.2 _]
    rw [ite_eq_left span]
    simp only [Nat.add_sub_cancel_left]
  have before : readI64 p.inner.memory p.inner.input.toNat = p.register := by
    rw [hr.native.memory_eq,inputNat]
    exact bytesRead
  have preserve := StateDispatchLength.lowMemory_register_frame p.inner innerWf hr.native.cellBound
    (by rw [innerSize]; exact stackBound) cs ss
  exact preserve.trans before

end WNear.Proofs.StateDispatchLengthOuter
