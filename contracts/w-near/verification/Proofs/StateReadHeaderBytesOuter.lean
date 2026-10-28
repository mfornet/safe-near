import Proofs.StateReadHeaderBytes
import Proofs.StateReadStorageOuterResult
import Proofs.StateReadStorageOuterPayload

/-! The proved storage/register pipeline recovers the model's original header bytes
in guest memory. Its representation is derived from the original encoded value,
not a guest-decode outcome or an execution assumption. -/
namespace WNear.Proofs.StateReadHeaderBytes
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] StateReadStorageOuter.finalMemory StateReadStorageOuter.callAfter

def pointer (p : StateReadStorageOuter.Layout) :=
  AllocateVector.result (StateReadRegisterOuter.actualVector (StateReadStorageOuter.actualRegister p)).toVector

theorem outer_header_at (p : StateReadStorageOuter.Layout) (hn : StateReadStorageOuter.Native p)
    (ha : p.allocator=1074896) (state : WNear.State) (he : p.bytes=WNear.header state) :
    At (StateReadStorageOuter.finalMemory p) (pointer p).toNat state := by
  intro i hi
  have length : p.bytes.length=29 := by rw [he,header_length]
  have byte := StateReadStorageOuter.finalMemory_payload p hn ha i (by omega)
  rw [he] at byte
  exact byte

theorem outer_header_reads (p : StateReadStorageOuter.Layout) (hn : StateReadStorageOuter.Native p)
    (ha : p.allocator=1074896) (state : WNear.State) (hw : state.WF) (he : p.bytes=WNear.header state) :
    readI32 (StateReadStorageOuter.finalMemory p) (pointer p).toNat=1 ∧
    (StateReadStorageOuter.finalMemory p).read8 ((pointer p).toNat+4)=97 ∧
    TotalSupply.U128At (StateReadStorageOuter.finalMemory p) ((pointer p).toNat+5) state.totalSupply ∧
    readI64 (StateReadStorageOuter.finalMemory p) ((pointer p).toNat+21)=UInt64.ofNat state.accountStorageUsage :=
  read_header _ _ state hw (outer_header_at p hn ha state he)

theorem callAfter_header (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : StateReadStorageOuter.Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (extra : Nat)
    (hn : StateReadStorageOuter.Native p) (ha : p.allocator=1074896)
    (hcode : StateReadStorageOuter.Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hd : callers.length+4<limits.maxCallDepth)
    (state : WNear.State) (hw : state.WF) (he : p.bytes=WNear.header state) :
    (StateReadStorageOuter.callAfter cfg s p ctx key).mems[p.memoryIndex]?=some (StateReadStorageOuter.finalMemory p) ∧
    p.bytes.length=29 ∧
    readI32 (StateReadStorageOuter.finalMemory p) (pointer p).toNat=1 ∧
    (StateReadStorageOuter.finalMemory p).read8 ((pointer p).toNat+4)=97 ∧
    TotalSupply.U128At (StateReadStorageOuter.finalMemory p) ((pointer p).toNat+5) state.totalSupply ∧
    readI64 (StateReadStorageOuter.finalMemory p) ((pointer p).toNat+21)=UInt64.ofNat state.accountStorageUsage := by
  have memory := StateReadStorageOuter.callAfter_memory cfg s limits inst height callers p ctx key extra hn ha hcode hm hg hd
  have length : p.bytes.length=29 := by rw [he,header_length]
  exact ⟨memory,length,outer_header_reads p hn ha state hw he⟩
end WNear.Proofs.StateReadHeaderBytes
