import Proofs.StateDispatchLengthFrame
import Proofs.StateDispatchLengthTail
import Proofs.StateDispatchLengthBorrow
import Proofs.StateDispatchPrefixHost

/-! Complete actual initialized register-length dispatcher f440. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 acquired high low checked arguments returned cleaned finalStore
set_option maxRecDepth 16384

 theorem checked_extCosts (s : Store NearState) (op : Nat) (p : Layout) :
    (checked s op p).host.extCosts = s.host.extCosts := by
  have h := congrArg NearState.extCosts (StateDispatchPrefix.acquired_host s op p.toLayout)
  simp only at h
  simpa only [checked,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,paid,chargedStore,chargeHost,
    low,high,storeI32_host,acquired] using h

 theorem resultValue_eq (s : Store NearState) (op : Nat) (p : Layout) :
    resultValue s op p = StateReadRegister.lengthValue s (register p) := by
  have h := congrArg NearState.registers (StateDispatchPrefix.acquired_host s op p.toLayout)
  simp only at h
  have hr : (checked s op p).host.registers = s.host.registers := by
    simpa only [checked,ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,paid,chargedStore,chargeHost,
      low,high,storeI32_host,acquired] using h
  simp only [resultValue,arguments,StateReadRegister.lengthValue,paid,chargedStore,chargeHost,hr]

 theorem checked_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (241 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest)) :
    (checked s cfg.regularOpCost p).host.gas.Credits (99 * cfg.regularOpCost + (checked s cfg.regularOpCost p).host.extCosts.cost "base" + rest) := by
  let op := cfg.regularOpCost
  let fee := s.host.extCosts.cost "base"
  have b0 : 114 * op + (127 * op + fee + rest) ≤ 241 * cfg.regularOpCost + fee + rest := by dsimp [op]; omega
  have b1 : 4 * op + (123 * op + fee + rest) ≤ 127 * op + fee + rest := by omega
  have b2 : 5 * op + (118 * op + fee + rest) ≤ 123 * op + fee + rest := by omega
  have b3 : 6 * op + (112 * op + fee + rest) ≤ 118 * op + fee + rest := by omega
  have b4 : 13 * op + (99 * op + fee + rest) ≤ 112 * op + fee + rest := by omega
  have ca : (acquired s op p).host.gas.Credits (127 * op + fee + rest) := by
    unfold acquired
    exact (StateDispatchPrefix.acquired_gas s op (127 * op + fee + rest) p.toLayout (hc.mono b0)).2.2
  have ch : (high s op p).host.gas.Credits (123 * op + fee + rest) := by
    unfold high
    rw [storeI32_host]
    exact paid_credits (acquired s op p) op 4 _ (ca.mono b1)
  have cl : (low s op p).host.gas.Credits (118 * op + fee + rest) := by
    unfold low
    rw [storeI32_host]
    exact paid_credits (high s op p) op 5 _ (ch.mono b2)
  have cs := paid_credits (low s op p) op 6 (112 * op + fee + rest) (cl.mono b3)
  have cc := ValueReturnOuter.nonnullAfter_credits (paid (low s op p) op 6) op (99 * op + fee + rest) (cs.mono b4)
  rw [checked_extCosts]
  unfold checked
  exact cc

 theorem borrow_after_eq (s : Store NearState) (op : Nat) (p : Layout) :
    StateDispatchLengthBorrow.after (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p) = checked s op p := by
  simp only [StateDispatchLengthBorrow.after,StateDispatchLengthBorrow.low,StateDispatchLengthBorrow.high,StateDispatchLengthBorrow.pointer,
    StateDispatchLengthBorrow.highMemory,checked,low,high,highMemory,borrowed]

 theorem borrow_pointer_eq (p : Layout) : StateDispatchLengthBorrow.pointer (acquiredMemory p) (scratch p) = borrowed p := rfl
 theorem borrow_selected_eq (p : Layout) : StateDispatchLengthBorrow.selected (acquiredMemory p) (scratch p) = selected p := rfl
 theorem borrow_frame_eq (frame : CallFrame) (p : Layout) (height : Nat) (code : List Instr) :
    StateDispatchLengthBorrow.finalFrame
      (StateDispatchPrefix.nested (acquiredFrame frame p) height code WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue)
      (acquiredMemory p) (scratch p) =
    StateDispatchPrefix.nested (copiedFrame frame p) height code WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue := by
  simp only [StateDispatchLengthBorrow.finalFrame,borrow_pointer_eq,StateDispatchPrefix.nested,emptyBlockFrame,copiedFrame]

 theorem tail_after_eq (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    StateDispatchLengthTail.after cfg (checked s cfg.regularOpCost p) p = finalStore cfg s p := by
  simp only [StateDispatchLengthTail.after,StateDispatchLengthTail.cleaned,StateDispatchLengthTail.returned,StateDispatchLengthTail.arguments,
    finalStore,cleaned,returned,arguments]

 theorem tail_value_eq (s : Store NearState) (op : Nat) (p : Layout) :
    StateDispatchLengthTail.value (checked s op p) op p = resultValue s op p := by
  simp only [StateDispatchLengthTail.value,StateDispatchLengthTail.arguments,resultValue,arguments]

 theorem frame_eq (frame : CallFrame) (p : Layout) (result : UInt64) :
    StateDispatchLengthTail.finalFrame (copiedFrame frame p) p result = finalFrame frame p result := rfl

/-- Full accepted f440 body: the original interface/counter/scratch resources
select real lookup, acquisition, host read, release and result return. -/
theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (p : Layout) (post : Post)
    (hr : Ready s limits frame callers p extra)
    (hc : s.host.gas.Credits (241 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s p) limits
      (base.toArray.push (.i64 (resultValue s cfg.regularOpCost p)))
      (finalFrame frame p (resultValue s cfg.regularOpCost p)) callers suffix)) rest post) :
    WP cfg (fuel + 162) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDispatchLength.body ++ suffix)))
      (241 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest) post := by
  let op := cfg.regularOpCost
  have hsize2 : 2 < frame.locals.size := by have := hr.localSize; omega
  have hsize0 : 0 < frame.locals.size := by have := hr.localSize; omega
  have d1 : callers.length + 1 < limits.maxCallDepth := by have := hr.prefixReady.depth; omega
  have d2 : callers.length + 2 < limits.maxCallDepth := by have := hr.prefixReady.depth; omega
  have cutPrefix : 114 * op + (127 * op + s.host.extCosts.cost "base" + rest) ≤ 241 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest := by dsimp [op]; omega
  have cutBorrow : 28 * cfg.regularOpCost + (99 * op + s.host.extCosts.cost "base" + rest) ≤ 127 * op + s.host.extCosts.cost "base" + rest := by dsimp [op]; omega
  have eqBorrow : 28 * cfg.regularOpCost + (99 * op + (s.host.extCosts.cost "base" + rest)) = 127 * op + (s.host.extCosts.cost "base" + rest) := by dsimp [op]; omega
  have eqPrefix : 114 * cfg.regularOpCost + (127 * op + (s.host.extCosts.cost "base" + rest)) = 241 * cfg.regularOpCost + (s.host.extCosts.cost "base" + rest) := by dsimp [op]; omega
  have hchecked := hr.code.checked s op p frame.inst extra
  have gh := checked_global s op p hr.prefixReady.global
  have hs1 : (copiedFrame frame p).locals[1]? = some (.i32 p.input) := by
    simpa [copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.inputLocal
  have hs2 : (copiedFrame frame p).locals[2]? = some (.i32 (scratch p)) := by
    simp [copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,scratch,hsize2]
  have hsSize : 5 ≤ (copiedFrame frame p).locals.size := by
    simpa [copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.localSize
  have tn : WP cfg fuel (.next (atCode (StateDispatchLengthTail.after cfg (checked s op p) p) limits
      (base.toArray.push (.i64 (StateDispatchLengthTail.value (checked s op p) op p)))
      (StateDispatchLengthTail.finalFrame (copiedFrame frame p) p (StateDispatchLengthTail.value (checked s op p) op p)) callers suffix)) rest post := by
    simpa only [tail_after_eq,tail_value_eq,frame_eq,op] using hnext
  have tail := StateDispatchLengthTail.wp_tail cfg extra fuel rest (checked s op p) limits base (copiedFrame frame p) callers suffix p {p.global with value := .i32 (scratch p)} post
    hchecked hs1 hs2 hsSize (checked_memory s op p hr.prefixReady.memory) gh rfl hr.cellBound hr.inputBound hr.vtableBound hr.releaseBound hr.counterBound
    d2 (checked_credits cfg s p rest hc) tn
  let gf := StateDispatchPrefix.nested (acquiredFrame frame p) base.toArray.size suffix WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue
  have gaFields := StateDispatchPrefix.acquired_fields s op p.toLayout
  have gam : (acquired s op p).modules[gf.inst]? = some p.mi := by
    have eqm : (acquired s op p).modules = s.modules := by simpa only [acquired] using gaFields.2.1
    rw [eqm]
    exact hr.code.prefixCode.module
  have gaf : (acquired s op p).funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction) := by
    have eqf : (acquired s op p).funcs = s.funcs := by simpa only [acquired] using gaFields.1
    rw [eqf]; exact hr.code.nonnullFunction
  have gamem : (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
    simpa only [acquired,acquiredMemory,scratch,StateDispatchPrefix.acquiredMemory] using StateDispatchPrefix.acquired_memory s op p.toLayout hr.prefixReady.memory
  have gs : gf.locals[2]? = some (.i32 (scratch p)) := by
    simp [gf,StateDispatchPrefix.nested,emptyBlockFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,scratch,
      hsize2]
  have gn : 0 < gf.locals.size := by
    simpa [gf,StateDispatchPrefix.nested,emptyBlockFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hsize0
  have ca : (acquired s op p).host.gas.Credits (127 * op + s.host.extCosts.cost "base" + rest) := by
    unfold acquired
    exact (StateDispatchPrefix.acquired_gas s op (127 * op + s.host.extCosts.cost "base" + rest) p.toLayout (hc.mono cutPrefix)).2.2
  have bn : WP cfg (fuel + 64) (.next (atCode
      (StateDispatchLengthBorrow.after (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)) limits
      (base.toArray.push (.i32 (StateDispatchLengthBorrow.selected (acquiredMemory p) (scratch p))))
      (StateDispatchLengthBorrow.finalFrame gf (acquiredMemory p) (scratch p)) callers
      (WNear.Binary.StateDispatchLength.dispatch ++ WNear.Binary.StateDispatchLength.cleanup)))
      (99 * op + s.host.extCosts.cost "base" + rest) post := by
    have fee : (checked s op p).host.extCosts = s.host.extCosts := checked_extCosts s op p
    simpa only [borrow_after_eq,borrow_selected_eq,gf,borrow_frame_eq,fee,op,Nat.add_assoc] using tail
  have borrow := StateDispatchLengthBorrow.wp_borrow cfg (fuel + 64) (99 * op + s.host.extCosts.cost "base" + rest) (acquired s op p) limits base gf callers
    (WNear.Binary.StateDispatchLength.dispatch ++ WNear.Binary.StateDispatchLength.cleanup) p.mi p.memoryIndex 430 (acquiredMemory p) (scratch p) post gs gn gam hr.code.prefixCode.memoryIndex gamem hr.code.nonnullIndex gaf
    hr.highBound hr.lowBound hr.selectBound hr.selectedNonzero d1 (ca.mono cutBorrow) bn
  have pn : WP cfg (fuel + 85) (.next (atCode (StateDispatchPrefix.acquired s op p.toLayout) limits base.toArray
      (StateDispatchPrefix.nested (StateDispatchPrefix.guardedFrame frame p.toLayout 2) base.toArray.size suffix
        WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue) callers WNear.Binary.StateDispatchLength.tail))
      (127 * op + s.host.extCosts.cost "base" + rest) post := by
    simpa only [WNear.Binary.StateDispatchLength.tail,WNear.Binary.StateDispatchLength.copyRecord,WNear.Binary.StateDispatchLength.selectRecord,
      gf,acquiredFrame,acquired,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      eqBorrow] using borrow
  have head := StateDispatchPrefix.wp_prefix cfg (fuel + 85) (127 * op + s.host.extCosts.cost "base" + rest) s limits base frame callers suffix
    WNear.Binary.StateDispatchLength.tail WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue p.toLayout 2 1055224 post hr.prefixReady
    (hc.mono cutPrefix) pn
  simpa only [WNear.Binary.StateDispatchLength.body,WNear.Binary.StateDispatchLength.prologue,WNear.Binary.StateDispatchLength.lookupAcquire,
    StateDispatchPrefix.body,StateDispatchPrefix.prologue,StateDispatchPrefix.inner,StateDispatchPrefix.lookup,StateDispatchPrefix.acquire,
    List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    eqPrefix] using head
end WNear.Proofs.StateDispatchLength
