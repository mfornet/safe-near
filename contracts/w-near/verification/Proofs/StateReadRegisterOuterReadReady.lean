import Proofs.StateReadRegisterOuterReadSnapshot

/-! Snapshot data suffices for all actual f435 preconditions; no execution hypothesis. -/
namespace WNear.Proofs.StateReadRegisterOuterReadMemory
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32

theorem Snapshot.ready {p : StateDispatchRead.Layout} {bytes : List UInt8} {register : UInt64} {pointer vtable : UInt32}
    (hn : Snapshot p bytes register pointer vtable)
    (s : Store NearState) (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (extra : Nat)
    (hcode : StateDispatchRead.Code s p frame.inst extra)
    (h0 : frame.locals[0]?=some (.i32 p.interface))
    (h1 : frame.locals[1]?=some (.i32 p.inputRegister))
    (h2 : frame.locals[2]?=some (.i32 p.inputPointer))
    (hs : 5≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global)
    (hv : p.global.value=.i32 p.sp)
    (hr : s.host.registers register.toNat=some bytes)
    (hd : callers.length+3<limits.maxCallDepth) :
    StateDispatchRead.Ready s limits frame callers p bytes extra  :=  by
  have hstate  :=  hn.stateBound
  have hscratch  :=  hn.scratch_bound
  have a  :=  StateDispatchLength.acquiredMemory_specs (StateDispatchRead.asLength p) hn.wf
    (by change 1074908≤p.memory.byteSize; omega) (by change (StateDispatchRead.scratch p).toNat+8≤p.memory.byteSize;omega)
  have ah : (StateDispatchRead.acquiredMemory p).byteSize=p.memory.byteSize  :=  a.2.1
  have ahw : (StateDispatchRead.acquiredMemory p).wf  :=  a.1
  have high  :=  writeI32_spec (StateDispatchRead.acquiredMemory p) ((StateDispatchRead.scratch p).toNat+12)
    (readI32 (StateDispatchRead.acquiredMemory p) ((StateDispatchRead.scratch p).toNat+4)) ahw (by rw [ah];omega)
  have hh : (StateDispatchRead.highMemory p).byteSize=p.memory.byteSize  :=  high.2.1.trans ah
  have low  :=  hn.low_shape
  have payload : (StateDispatchRead.ptr p).toNat+bytes.length≤(StateDispatchRead.lowMemory p).byteSize  :=  by
    rw [hn.ptr_nat , low.2.1];exact hn.payloadBound
  have copied  :=  Memory.writeList_spec bytes (StateDispatchRead.lowMemory p) (StateDispatchRead.ptr p).toNat low.1 payload
  have copySize : (StateDispatchRead.readMemory p bytes).byteSize=p.memory.byteSize  :=  copied.2.1.trans low.2.1
  have sn  :=  hn.scratch_nat
  have sl  :=  hn.spLower
  have sw  :=  p.sp.toNat_lt
  have sa  :=  hn.aligned
  have aligned : (StateDispatchRead.scratch p).toNat%16=0  :=  by omega
  have orWord  :=  or4_aligned (StateDispatchRead.scratch p) aligned (by omega)
  have accepted : Numeric.irelop32 .ge_s (ValueReturnAcquire.nextCount p.memory 1074904) 1=true  :=  by
    unfold ValueReturnAcquire.nextCount
    change Numeric.irelop32 .ge_s (readI32 p.memory 1074904+1) 1=true
    rw [hn.counterZero]
    rfl
  refine {
    code := hcode , prefixReady := ?_ , registerLocal := h1 , pointerLocal := h2 , localSize := hs ,
    highBound := ?_ , lowBound := ?_ , selectBound := ?_ , selectedNonzero := ?_ , cellBound := ?_ ,
    registerBound := ?_ , pointerBound := ?_ , vtableBound := ?_ , registerValue := ?_ , payloadBound := payload ,
    releaseBound := ?_ , counterBound := ?_}
  · refine {
      code := hcode.prefixCode , interfaceLocal := h0 , localSize := by omega , slotNe := by decide ,
      memory := hm , global := hg , sp := hv , memoryWf := hn.wf , interfaceBound := ?_ , interfaceRead := ?_ ,
      threadBound := by omega , threadStatus := hn.threadStatus , cellBound := by omega ,
      acquireOutBound := ?_ , countAccepted := accepted , depth := hd}
    · rw [hn.interface];exact hn.interfaceBound
    · rw [hn.interface];exact hn.interfaceRead
    · change (StateDispatchRead.scratch p).toNat+8≤p.memory.byteSize;omega
  · rw [ah];exact hscratch
  · rw [hh];omega
  · rw [hn.borrowed , low.2.1];exact le_trans (by decide) hstate
  · rw [hn.selected];decide
  · rw [hn.selected , low.2.1];exact hstate
  · rw [low.2.1];have := hn.registerEnd;omega
  · rw [low.2.1];have := hn.pointerEnd;omega
  · rw [hn.vtable , low.2.1];exact hn.vtableBound
  · rw [hn.register_eq];exact hr
  · rw [orWord , copySize];omega
  · rw [hn.counter , copySize];exact le_trans (by decide) hstate
end WNear.Proofs.StateReadRegisterOuterReadMemory
