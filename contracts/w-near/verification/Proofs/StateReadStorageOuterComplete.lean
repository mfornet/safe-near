import Proofs.StateReadStorageOuterCall
import Proofs.StateReadStorageOuterResult
import Proofs.StateReadStorageOuterPayload

/-! Typed f548 execution and its original-storage-byte output endpoint. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

theorem callAfter_output (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hd : callers.length+4<limits.maxCallDepth)
    (hs : (scratch p+16+8).toNat+4≤p.out548.toNat ∨ p.out548.toNat+8≤(scratch p+16+8).toNat) :
    (callAfter cfg s p ctx key).mems[p.memoryIndex]?=some (finalMemory p) ∧
    readI32 (finalMemory p) p.out548.toNat=
      AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector ∧
    readI32 (finalMemory p) (p.out548.toNat+4)=p.size ∧
    readI32 (finalMemory p) (p.out548.toNat+8)=p.size ∧
    ∀ i, i<p.bytes.length → (finalMemory p).read8
      ((AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat+i)=p.bytes[i]! := by
  have record := finalMemory_low_record p hn ha
  exact ⟨callAfter_memory cfg s limits inst height callers p ctx key extra hn ha hcode hm hg hd,
    record.1,record.2,finalMemory_length p hn ha hs,finalMemory_payload p hn ha⟩
end WNear.Proofs.StateReadStorageOuter
