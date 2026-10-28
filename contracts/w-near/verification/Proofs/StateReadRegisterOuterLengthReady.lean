import Proofs.StateReadRegisterOuterCode
import Proofs.StateReadRegisterOuterSetupFrame

/-! Original523 arrays and native words supply the complete actual524 Ready. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI64 registerMemory

theorem Code.length_ready (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s frame.inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (h0 : frame.locals[0]?=some (.i32 (scratch p+8)))
    (h1 : frame.locals[1]?=some (.i64 p.register)) (hs : 3≤frame.locals.size)
    (hd : callers.length+4<limits.maxCallDepth) :
    StateDispatchLengthOuter.Ready (lengthArguments s cfg.regularOpCost p) limits frame callers (actualLength p) extra := by
  have fields := lengthArguments_fields s cfg.regularOpCost p
  have code := (hcode.lengthCode s frame.inst p extra hn ha).transport s (lengthArguments s cfg.regularOpCost p)
    (actualLength p).inner frame.inst extra fields.1 fields.2.1 fields.2.2
  have shape := registerMemory_spec p hn
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have outBound : (scratch p+8).toNat+16≤(registerMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.1];omega
  have inputBound : (scratch p-16).toNat+16≤(registerMemory p).byteSize := by
    rw [shape.2.1,nums.2.1];omega
  have me : (lengthArguments s cfg.regularOpCost p).mems[(actualLength p).inner.memoryIndex]?=some (actualLength p).memory :=
    lengthArguments_memory s cfg.regularOpCost p hm
  have ge : (lengthArguments s cfg.regularOpCost p).globals[(actualLength p).inner.globalIndex]?=some (actualLength p).global :=
    lengthArguments_global s cfg.regularOpCost p hg
  have fn : (lengthArguments s cfg.regularOpCost p).funcs[440]?=
      some (.wasm WNear.Binary.StateDispatchLength.signature frame.inst WNear.Binary.StateDispatchLength.function) := by
    rw [fields.1];exact hcode.innerLengthFunction
  exact ⟨code,length_native p hn,h0,h1,hs,me,ge,rfl,shape.1,outBound,inputBound,
    hcode.innerLengthIndex,fn,hd⟩
end WNear.Proofs.StateReadRegisterOuter
