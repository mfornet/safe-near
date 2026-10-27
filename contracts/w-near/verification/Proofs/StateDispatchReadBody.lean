import Proofs.StateDispatchReadFrame
import Proofs.StateDispatchReadTail
import Proofs.StateDispatchReadBorrow
import Proofs.StateDispatchReadHost

/-! Complete actual initialized read-register dispatcher f435. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 acquired checked arguments returned
attribute [local irreducible] StateDispatchReadBorrow.high StateDispatchReadBorrow.low StateDispatchReadBorrow.after
set_option maxRecDepth 16384

def finalStore (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :=
  StateDispatchReadTail.after cfg (checked s cfg.regularOpCost p) p bytes
def finalFrame (frame : CallFrame) (p : Layout) := StateDispatchReadTail.argumentFrame (copiedFrame frame p) p

private theorem borrow_credits (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) (rest : Nat)
    (hc : s.host.gas.Credits (30 * op + rest)) :
    (StateDispatchReadBorrow.after s op index memory scratch).host.gas.Credits rest := by
  have b0 : 4 * op + (26 * op + rest) ≤ 30 * op + rest := by omega
  have b1 : 5 * op + (21 * op + rest) ≤ 26 * op + rest := by omega
  have b2 : 2 * op + (19 * op + rest) ≤ 21 * op + rest := by omega
  have b3 : 6 * op + (13 * op + rest) ≤ 19 * op + rest := by omega
  have ch : (StateDispatchReadBorrow.high s op index memory scratch).host.gas.Credits (26 * op + rest) := by
    unfold StateDispatchReadBorrow.high
    rw [storeI32_host]
    exact paid_credits s op 4 _ (hc.mono b0)
  have cl : (StateDispatchReadBorrow.low s op index memory scratch).host.gas.Credits (21 * op + rest) := by
    unfold StateDispatchReadBorrow.low
    rw [storeI32_host]
    exact paid_credits _ op 5 _ (ch.mono b1)
  have cs := paid_credits (StateDispatchReadBorrow.low s op index memory scratch) op 2 (19 * op + rest) (cl.mono b2)
  unfold StateDispatchReadBorrow.after
  exact ValueReturnOuter.nonnullAfter_credits (paid (paid (StateDispatchReadBorrow.low s op index memory scratch) op 2) op 6) op rest
    (paid_credits _ op 6 (13 * op + rest) (cs.mono b3))

 theorem checked_fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    RegisterRead.readCost (checked s cfg.regularOpCost p).host bytes.length = RegisterRead.readCost s.host bytes.length := by
  have h := congrArg NearState.extCosts (checked_host s cfg.regularOpCost p)
  simp only at h
  simp only [RegisterRead.readCost,h]

 theorem checked_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) (rest : Nat)
    (hc : s.host.gas.Credits (237 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest)) :
    (checked s cfg.regularOpCost p).host.gas.Credits (93 * cfg.regularOpCost + RegisterRead.readCost (checked s cfg.regularOpCost p).host bytes.length + rest) := by
  let op := cfg.regularOpCost
  have b0 : 114 * op + (123 * op + RegisterRead.readCost s.host bytes.length + rest) ≤ 237 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest := by dsimp [op]; omega
  have b1 : 30 * op + (93 * op + RegisterRead.readCost s.host bytes.length + rest) ≤ 123 * op + RegisterRead.readCost s.host bytes.length + rest := by omega
  have ca := (StateDispatchPrefix.acquired_gas s op (123 * op + RegisterRead.readCost s.host bytes.length + rest) p.toLayout (hc.mono b0)).2.2
  rw [checked_fee]
  unfold checked
  simpa only [acquired,op] using borrow_credits (StateDispatchPrefix.acquired s op p.toLayout) op p.memoryIndex (acquiredMemory p) (scratch p) _ (ca.mono b1)

 theorem borrow_selected_eq (p : Layout) : StateDispatchReadBorrow.selected (acquiredMemory p) (scratch p) = selected p := rfl
 theorem borrow_frame_eq (frame : CallFrame) (p : Layout) (height : Nat) (code : List Instr) :
    StateDispatchReadBorrow.finalFrame
      (StateDispatchPrefix.nested (acquiredFrame frame p) height code WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue)
      (acquiredMemory p) (scratch p) =
    StateDispatchPrefix.nested (copiedFrame frame p) height code WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue := by
  simp only [StateDispatchReadBorrow.finalFrame,StateDispatchReadBorrow.copiedFrame,StateDispatchPrefix.nested,emptyBlockFrame,copiedFrame]

/-- Full accepted f435 body: the original interface/counter/scratch resources
select real lookup, acquisition, host read, release and result return. -/
theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (p : Layout)
    (bytes : List UInt8) (post : Post)
    (hr : Ready s limits frame callers p bytes extra)
    (hc : s.host.gas.Credits (237 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s p bytes) limits
      base.toArray
      (finalFrame frame p) callers suffix)) rest post) :
    WP cfg (fuel + 159) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDispatchRead.body ++ suffix)))
      (237 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest) post := by
  let op := cfg.regularOpCost
  have hsize3 : 3 < frame.locals.size := by have := hr.localSize; omega
  have hsize4 : 4 < frame.locals.size := by have := hr.localSize; omega
  have d1 : callers.length + 1 < limits.maxCallDepth := by have := hr.prefixReady.depth; omega
  have d2 : callers.length + 2 < limits.maxCallDepth := by have := hr.prefixReady.depth; omega
  have cutPrefix : 114 * op + (123 * op + RegisterRead.readCost s.host bytes.length + rest) ≤ 237 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest := by dsimp [op]; omega
  have cutBorrow : 30 * cfg.regularOpCost + (93 * op + RegisterRead.readCost s.host bytes.length + rest) ≤ 123 * op + RegisterRead.readCost s.host bytes.length + rest := by dsimp [op]; omega
  have eqBorrow : 30 * cfg.regularOpCost + (93 * op + (RegisterRead.readCost s.host bytes.length + rest)) = 123 * op + (RegisterRead.readCost s.host bytes.length + rest) := by dsimp [op]; omega
  have eqPrefix : 114 * cfg.regularOpCost + (123 * op + (RegisterRead.readCost s.host bytes.length + rest)) = 237 * cfg.regularOpCost + (RegisterRead.readCost s.host bytes.length + rest) := by dsimp [op]; omega
  have hchecked := hr.code.checked s op p frame.inst extra
  have gh := checked_global s op p hr.prefixReady.global
  have hs1 : (copiedFrame frame p).locals[1]? = some (.i32 p.inputRegister) := by
    simpa [copiedFrame,StateDispatchReadBorrow.finalFrame,StateDispatchReadBorrow.copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.registerLocal
  have hs2 : (copiedFrame frame p).locals[2]? = some (.i32 p.inputPointer) := by
    simpa [copiedFrame,StateDispatchReadBorrow.finalFrame,StateDispatchReadBorrow.copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.pointerLocal
  have hs3 : (copiedFrame frame p).locals[3]? = some (.i32 (scratch p)) := by
    simp [copiedFrame,StateDispatchReadBorrow.finalFrame,StateDispatchReadBorrow.copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,scratch,hsize3]
  have hsSize : 5 ≤ (copiedFrame frame p).locals.size := by
    simpa [copiedFrame,StateDispatchReadBorrow.finalFrame,StateDispatchReadBorrow.copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.localSize
  have hs0 : (copiedFrame frame p).locals[0]? = some (.i32 0) := by
    simp [copiedFrame,StateDispatchReadBorrow.finalFrame,StateDispatchReadBorrow.copiedFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,show 0 < frame.locals.size by have := hr.localSize; omega]
  have rcheck : (checked s op p).host.registers (register p).toNat = some bytes := by
    have h := congrArg NearState.registers (checked_host s op p)
    simp only at h
    rw [h]; exact hr.registerValue
  have tn : WP cfg fuel (.next (atCode (StateDispatchReadTail.after cfg (checked s op p) p bytes) limits
      base.toArray (StateDispatchReadTail.argumentFrame (copiedFrame frame p) p) callers suffix)) rest post := by
    simpa only [finalStore,finalFrame,op] using hnext
  have tail := StateDispatchReadTail.wp_tail cfg extra fuel rest (checked s op p) limits base (copiedFrame frame p) callers suffix p {p.global with value := .i32 (scratch p)} bytes post
    hchecked hs1 hs2 hs0 hs3 hsSize (checked_memory s op p hr.prefixReady.memory) gh rfl hr.cellBound hr.registerBound hr.pointerBound hr.vtableBound
    rcheck hr.payloadBound hr.releaseBound hr.counterBound d2 (checked_credits cfg s p bytes rest hc) tn
  let gf := StateDispatchPrefix.nested (acquiredFrame frame p) base.toArray.size suffix WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue
  have gaFields := StateDispatchPrefix.acquired_fields s op p.toLayout
  have gam : (acquired s op p).modules[gf.inst]? = some p.mi := by
    have eqm : (acquired s op p).modules = s.modules := by simpa only [acquired,acquired] using gaFields.2.1
    rw [eqm]
    exact hr.code.prefixCode.module
  have gaf : (acquired s op p).funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction) := by
    have eqf : (acquired s op p).funcs = s.funcs := by simpa only [acquired,acquired] using gaFields.1
    rw [eqf]; exact hr.code.nonnullFunction
  have gamem : (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
    exact acquired_memory s op p hr.prefixReady.memory
  have gs : gf.locals[3]? = some (.i32 (scratch p)) := by
    simp [gf,StateDispatchPrefix.nested,emptyBlockFrame,acquiredFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,scratch,scratch,
      hsize3]
  have ca : (acquired s op p).host.gas.Credits (123 * op + RegisterRead.readCost s.host bytes.length + rest) := by
    unfold acquired
    simpa only [acquired] using (StateDispatchPrefix.acquired_gas s op (123 * op + RegisterRead.readCost s.host bytes.length + rest) p.toLayout (hc.mono cutPrefix)).2.2
  have bn : WP cfg (fuel + 59) (.next (atCode
      (StateDispatchReadBorrow.after (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)) limits
      (base.toArray.push (.i32 (StateDispatchReadBorrow.selected (acquiredMemory p) (scratch p))))
      (StateDispatchReadBorrow.finalFrame gf (acquiredMemory p) (scratch p)) callers
      (WNear.Binary.StateDispatchRead.dispatch ++ WNear.Binary.StateDispatchRead.cleanup)))
      (93 * op + RegisterRead.readCost s.host bytes.length + rest) post := by
    rw [checked_fee] at tail
    simpa only [checked,borrow_selected_eq,gf,borrow_frame_eq,op,Nat.add_assoc] using tail
  have borrow := StateDispatchReadBorrow.wp_borrow cfg (fuel + 59) (93 * op + RegisterRead.readCost s.host bytes.length + rest) (acquired s op p) limits base gf callers
    (WNear.Binary.StateDispatchRead.dispatch ++ WNear.Binary.StateDispatchRead.cleanup) p.mi p.memoryIndex 430 (acquiredMemory p) (scratch p) post gs (by simpa [gf,StateDispatchPrefix.nested,emptyBlockFrame,acquiredFrame,acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using (show 5 ≤ frame.locals.size by have := hr.localSize; omega)) gam hr.code.prefixCode.memoryIndex gamem hr.code.nonnullIndex gaf
    hr.highBound hr.lowBound hr.selectBound hr.selectedNonzero d1 (ca.mono cutBorrow) bn
  have pn : WP cfg (fuel + 82) (.next (atCode (StateDispatchPrefix.acquired s op p.toLayout) limits base.toArray
      (StateDispatchPrefix.nested (StateDispatchPrefix.guardedFrame frame p.toLayout 3) base.toArray.size suffix
        WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue) callers WNear.Binary.StateDispatchRead.tail))
      (123 * op + RegisterRead.readCost s.host bytes.length + rest) post := by
    simpa only [WNear.Binary.StateDispatchRead.tail,WNear.Binary.StateDispatchRead.copyRecord,WNear.Binary.StateDispatchRead.selectRecord,
      gf,acquiredFrame,acquiredFrame,acquired,acquired,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      eqBorrow] using borrow
  have head := StateDispatchPrefix.wp_prefix cfg (fuel + 82) (123 * op + RegisterRead.readCost s.host bytes.length + rest) s limits base frame callers suffix
    WNear.Binary.StateDispatchRead.tail WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue p.toLayout 3 1055160 post hr.prefixReady
    (hc.mono cutPrefix) pn
  simpa only [WNear.Binary.StateDispatchRead.body,WNear.Binary.StateDispatchRead.prologue,WNear.Binary.StateDispatchRead.lookupAcquire,
    StateDispatchPrefix.body,StateDispatchPrefix.prologue,StateDispatchPrefix.inner,StateDispatchPrefix.lookup,StateDispatchPrefix.acquire,
    List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    eqPrefix] using head
end WNear.Proofs.StateDispatchRead
