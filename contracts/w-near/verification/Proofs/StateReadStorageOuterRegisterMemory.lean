import Proofs.StateReadStorageOuterRegisterReady

/-! Complete actual523 memory after the storage read. Register presence, code,
allocation domain and all current resource lookups are derived from original548 data. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] registered registerArguments registeredMemory actualRegister StateReadRegisterOuter.callAfter StateReadRegisterOuter.copiedMemory

theorem registered_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (hd : callers.length+4<limits.maxCallDepth) :
    (registered cfg s p ctx key).mems[p.memoryIndex]?=some (registeredMemory p) := by
  have ready := register_call_resources cfg extra s inst p ctx key hn ha hcode hm hg
  have root : (actualRegister p).allocator=1074896 := by simpa only [actualRegister,registerTemplate] using ha
  have mem := StateReadRegisterOuter.callAfter_memory cfg (registerArguments cfg s p ctx key) limits inst height callers
    (actualRegister p) extra (register_native p hn ha) root ready.1 ready.2.1 ready.2.2.1 ready.2.2.2.2.1 hd
  have index : (actualRegister p).memoryIndex=p.memoryIndex := by simp only [actualRegister,registerTemplate]
  rw [index] at mem
  simpa only [registered,registeredMemory] using mem
end WNear.Proofs.StateReadStorageOuter
