import Proofs.StateReadRegisterOuterLengthReady

/-! The real524 observation is the original present register length, and its
actual returned memory is the deterministic523 lengthMemory. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] lengthArguments looked lengthMemory

theorem length_result_value (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    StateDispatchLengthOuter.resultValue
      (StateDispatchLengthOuter.entered (lengthArguments s cfg.regularOpCost p) cfg.regularOpCost) (actualLength p)=
      UInt64.ofNat p.bytes.length := by
  let a := lengthArguments s cfg.regularOpCost p
  let leaf := StateDispatchLengthOuter.leafFrame inst height (actualLength p)
  let active := StateDispatchLengthOuter.entered a cfg.regularOpCost
  have locals : 3≤leaf.locals.size := by simp [leaf,StateDispatchLengthOuter.leafFrame]
  have ready := Code.length_ready cfg s limits leaf callers p extra hn ha hcode hm hg rfl rfl locals hd
  have enteredReady : StateDispatchLengthOuter.Ready active limits leaf callers (actualLength p) extra :=
    (ready.charge a cfg.regularOpCost limits leaf callers (actualLength p) extra).charge
      (chargedStore a cfg.regularOpCost) (10*cfg.regularOpCost) limits leaf callers (actualLength p) extra
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have above := hn.staticAbove
  have stackBound : 32≤(actualLength p).sp.toNat := by change 32≤(scratch p).toNat;rw [nums.1];omega
  have counterSep : (actualLength p).sp.toNat≤1074904 ∨ 1074916≤(actualLength p).sp.toNat := by
    left;change (scratch p).toNat≤1074904;rw [nums.1];omega
  have value := StateDispatchLengthOuter.resultValue_eq active limits leaf callers (actualLength p) extra
    enteredReady stackBound counterSep
  have register : active.host.registers p.register.toNat=some p.bytes := by
    change a.host.registers p.register.toNat=some p.bytes
    rw [show a.host.registers=s.host.registers from lengthArguments_registers s cfg.regularOpCost p]
    exact hr
  have registerId : (actualLength p).register=p.register := rfl
  simpa only [StateReadRegister.lengthValue,registerId,register,Option.map_some,Option.getD_some] using value

theorem looked_memory (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    (looked cfg s p).mems[p.memoryIndex]?=some (lengthMemory p) := by
  let active := StateDispatchLengthOuter.entered (lengthArguments s cfg.regularOpCost p) cfg.regularOpCost
  have me : active.mems[(actualLength p).inner.memoryIndex]?=some (actualLength p).memory :=
    lengthArguments_memory s cfg.regularOpCost p hm
  have result := StateDispatchLengthOuter.finalStore_memory cfg active (actualLength p)
    hcode.prefixCode.memoryIndex me (length_native p hn)
  have value := length_result_value cfg s limits inst height callers p extra hn ha hcode hm hg hr hd
  unfold StateDispatchLengthOuter.resultMemory at result
  rw [value] at result
  have index : (actualLength p).inner.memoryIndex=p.memoryIndex := rfl
  rw [index] at result
  simpa only [looked,StateDispatchLengthOuter.callAfter,lengthMemory,active] using result
end WNear.Proofs.StateReadRegisterOuter
