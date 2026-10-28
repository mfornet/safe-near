import Proofs.StateReadRegisterOuterVectorCode
import Proofs.StateReadRegisterOuterFrame
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] looked vectorArguments actualVector lengthMemory actualLength vectorMemoryTemplate vectorGrown registerMemory

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem vector_mems (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (vectorArguments cfg s p).mems=(looked cfg s p).mems := by
  unfold vectorArguments guarded
  rw [paid_mems,paid_mems]

theorem vector_call_resources (cfg : WasmConfig) (extra : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (p : Layout) (hn : Native p) (hcode : Code s frame.inst p extra)
    (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    let q := actualVector p
    AllocateVectorOuter.Code (vectorArguments cfg s p) frame.inst q ∧
    (vectorArguments cfg s p).mems[q.memoryIndex]?=some q.memory ∧
    (vectorArguments cfg s p).globals[q.globalIndex]?=some q.global687 ∧
    q.global687.value=.i32 q.sp687 ∧
    (vectorArguments cfg s p).funcs[p.address687]?=some (.wasm WNear.Binary.AllocateVectorOuter.signature frame.inst WNear.Binary.AllocateVectorOuter.function) := by
  let q := actualVector p
  have fields := vectorArguments_fields cfg s p
  have cd : AllocateVectorOuter.Code (vectorArguments cfg s p) frame.inst q :=
    (hcode.vectorCode s frame.inst p extra hn).transport s _ frame.inst q fields.1 fields.2.1 fields.2.2
  have lm := looked_memory cfg s limits frame.inst base.length callers p extra hn haRoot hcode hm hg hr hd
  have ma : (vectorArguments cfg s p).mems[q.memoryIndex]?=some q.memory := by
    have same : (vectorArguments cfg s p).mems[p.memoryIndex]?=some (lengthMemory p) := by
      rw [vector_mems];exact lm
    simpa only [q,actualVector,vectorMemoryTemplate] using same
  have ga : (vectorArguments cfg s p).globals[q.globalIndex]?=some q.global687 := by
    simpa only [q,actualVector,vectorMemoryTemplate] using vectorArguments_global cfg s p hn hg
  have gv : q.global687.value=.i32 q.sp687 := by
    simp only [q,actualVector,vectorMemoryTemplate,hn.vectorGlobal]
  have hf : (vectorArguments cfg s p).funcs[p.address687]?=some (.wasm WNear.Binary.AllocateVectorOuter.signature frame.inst WNear.Binary.AllocateVectorOuter.function) := by
    rw [fields.1];exact hcode.function687
  exact ⟨cd,ma,ga,gv,hf⟩
end WNear.Proofs.StateReadRegisterOuter
