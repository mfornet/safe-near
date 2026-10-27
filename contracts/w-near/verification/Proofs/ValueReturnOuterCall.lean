import Proofs.ValueReturnOuterBody
import Proofs.ValueReturnOuterPrefix
import Proofs.ValueReturnOuterDispatchTail
import Proofs.ValueReturnOuterCodeFrame
import Proofs.ValueReturnOuterGlobals
import Proofs.ValueReturnOuterMemory

/-! Composition of the actual accepted f456 path, from primitive resources. -/
namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.ValueReturnOuter
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem borrowHigh_eq (s : Store NearState) (op : Nat) (p : Layout) :
    borrowHigh (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) = high s op p := rfl

theorem borrowLow_eq (s : Store NearState) (op : Nat) (p : Layout) :
    borrowLow (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p) = low s op p := rfl

theorem borrowStatus_eq (s : Store NearState) (op : Nat) (p : Layout) :
    borrowStatus (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p) = status s op p := rfl

theorem borrowAfter_eq (s : Store NearState) (op : Nat) (p : Layout) :
    borrowAfter (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p) = dispatchBefore s op p := rfl

theorem borrowFrame_nested (frame : CallFrame) (height : Nat) (code : List Instr) (p : Layout) :
    borrowFrame (nested (guardedFrame frame p) height code) (highMemory p) (scratch p) =
      nested (statusFrame frame p) height code := rfl

/-- The complete actual post-acquisition tail, assembled from separately checked
23-step scalar/nonnull and59-step dispatch/cleanup kernel proofs. -/
theorem wp_tail (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hr : Ready cfg extra s limits frame callers p) (cp : PhaseCredits cfg s p rest)
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s p) limits base.toArray (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 82) (.next (atCode (acquired s cfg.regularOpCost p) limits base.toArray
      (nested (guardedFrame frame p) base.toArray.size code) callers
      (WNear.Binary.ValueReturnOuter.saveBorrow ++ WNear.Binary.ValueReturnOuter.nonnull ++
        WNear.Binary.ValueReturnDispatch.dispatch ++ WNear.Binary.ValueReturnOuter.cleanup)))
      (123 * cfg.regularOpCost + fee cfg s p + rest) post := by
  let op := cfg.regularOpCost
  have hsize := hr.localSize
  have hdepth := hr.depth
  have h0 : 0 < frame.locals.size := by omega
  have h2 : 2 < frame.locals.size := by omega
  have fs := frames frame p hr.interfaceLocal hr.sliceLocal hr.localSize
  have hzero : (statusFrame frame p).locals[0]? = some (.i32 0) := by
    simp [statusFrame, pointerFrame, guardedFrame, reservedFrame, h0]
  have hscratch : (statusFrame frame p).locals[2]? = some (.i32 (scratch p)) := by
    simp [statusFrame, pointerFrame, guardedFrame, reservedFrame, h2]
  have cd0 := Code.dispatch s op p frame.inst extra hr.code
  have cd : Code (dispatchBefore s op p) p (statusFrame frame p).inst extra := cd0
  have hg : (dispatchBefore s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    rw [dispatch_globals s op p hr.global]
    exact reserved_global s op p hr.global
  have tailRule := ValueReturnOuterDispatchTail.wp_tail cfg extra fuel rest (dispatchBefore s op p) limits base
    (statusFrame frame p) callers code p (selected p) (counter p) (lowMemory p) {p.global with value := .i32 (scratch p)} post
    cd hzero fs.2.2.2.2.1 hscratch fs.2.2.2.2.2.1 hr.dispatchMemoryLookup hg rfl
    hr.returnCellBound hr.sliceBound hr.vtableBound hr.receiverRead hr.vtableRead hr.elementRead hr.lengthRead hr.pointerRead
    hr.fixedLength hr.returnBound hr.returnLimit rfl hr.cleanupRecordBound hr.counterBound (by omega)
  have tailPaid := tailRule cp.c_dispatch
  have tailNext : WP cfg fuel (.next (atCode
      (cleanupAfter (ValueReturnDispatch.fragmentAfter cfg (dispatchBefore s op p) p.mi p.len p.ptr) op
        p.globalIndex p.memoryIndex (scratch p) (counter p) (lowMemory p)) limits base.toArray
      (ValueReturnDispatch.dispatchFrame (statusFrame frame p) (selected p)) callers code)) rest post := by
    simpa only [finalStore, returned, finalFrame, op] using hnext
  have tailProof := tailPaid tailNext
  let guard := nested (guardedFrame frame p) base.toArray.size code
  have ca0 := Code.acquired s op p frame.inst extra hr.code
  have ca : Code (acquired s op p) p guard.inst extra := ca0
  have hguardScratch : guard.locals[2]? = some (.i32 (scratch p)) := fs.2.2.1
  have hguardSize : 4 ≤ guard.locals.size := by simpa [guard, nested, emptyBlockFrame, guardedFrame, reservedFrame] using hr.localSize
  have hmem1 : (borrowHigh (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p)).mems[p.memoryIndex]? = some (highMemory p) := by
    rw [borrowHigh_eq]; exact hr.highMemoryLookup
  have hmem2 : (borrowStatus (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p)).mems[p.memoryIndex]? = some (lowMemory p) := by
    rw [borrowStatus_eq]
    rw [status, paid_mems]
    exact hr.lowMemoryLookup
  have scalarRule := wp_borrow_tail cfg (fuel + 59) (93 * op + fee cfg s p + rest) (acquired s op p) limits base guard callers
    (WNear.Binary.ValueReturnDispatch.dispatch ++ WNear.Binary.ValueReturnOuter.cleanup) (scratch p) p.mi p.memoryIndex 430 frame.inst
    (acquiredMemory p) (highMemory p) (lowMemory p) post
    hguardScratch hguardSize ca.module ca.memoryIndex hr.acquiredMemoryLookup hmem1 hmem2 hr.highBound hr.lowBound hr.selectBound
    hr.selectedNonzero ca.nonnullIndex ca.nonnullFunction (by omega)
  have scalarCredit : (acquired s op p).host.gas.Credits (30 * cfg.regularOpCost + (93 * op + fee cfg s p + rest)) := cp.c_acquired.mono (by dsimp [op]; omega)
  have scalarPaid := scalarRule scalarCredit
  have oneStack : (base ++ [Value.i32 (selected p)]).toArray = base.toArray.push (.i32 (selected p)) := by apply Array.toList_inj.mp; simp
  have scalarNext : WP cfg (fuel + 59) (.next (atCode
      (borrowAfter (acquired s op p) op p.memoryIndex (scratch p) (acquiredMemory p) (highMemory p)) limits
      (base ++ [Value.i32 (selected p)]).toArray (borrowFrame guard (highMemory p) (scratch p)) callers
      (WNear.Binary.ValueReturnDispatch.dispatch ++ WNear.Binary.ValueReturnOuter.cleanup))) (93 * op + fee cfg s p + rest) post := by
    rw [borrowAfter_eq, show borrowFrame guard (highMemory p) (scratch p) = nested (statusFrame frame p) base.toArray.size code from borrowFrame_nested frame _ code p, oneStack]
    exact tailProof
  have result := scalarPaid scalarNext
  have fuelEq : fuel + 59 + 23 = fuel + 82 := by omega
  have gasEq : 30 * cfg.regularOpCost + (93 * op + fee cfg s p + rest) = 123 * cfg.regularOpCost + fee cfg s p + rest := by dsimp [op]; omega
  have codeEq : (WNear.Binary.ValueReturnOuter.saveBorrow ++ WNear.Binary.ValueReturnOuter.nonnull ++
      (WNear.Binary.ValueReturnDispatch.dispatch ++ WNear.Binary.ValueReturnOuter.cleanup)) =
      (WNear.Binary.ValueReturnOuter.saveBorrow ++ WNear.Binary.ValueReturnOuter.nonnull ++ WNear.Binary.ValueReturnDispatch.dispatch ++ WNear.Binary.ValueReturnOuter.cleanup) := by simp only [List.append_assoc]
  exact cast_phase cfg _ _ _ _ (acquired s op p) limits base.toArray guard callers _ _ post fuelEq gasEq codeEq result

/-- Actual full accepted f456 body, including initialized lookup, borrowing,
value_return, release and restoration. No callee-execution premise remains. -/
theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hr : Ready cfg extra s limits frame callers p)
    (hc : s.host.gas.Credits (budget cfg s p + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s p) limits base.toArray (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 159) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnOuter.body ++ code))) (budget cfg s p + rest) post := by
  let op := cfg.regularOpCost
  have cp := phase_credits cfg extra rest s limits frame callers p hr hc
  have tail := wp_tail cfg extra fuel rest s limits base frame callers code p post hr cp hnext
  have prefixCredit : s.host.gas.Credits (114 * op + (123 * op + fee cfg s p + rest)) := hc.mono (by dsimp [op, budget]; omega)
  have prefixRule := ValueReturnOuterPrefix.wp_prefix cfg extra (fuel + 82) (123 * op + fee cfg s p + rest)
    s limits base frame callers code p post hr prefixCredit
  have prefixNext : WP cfg (fuel + 82) (.next (atCode (acquired s op p) limits base.toArray
      (ValueReturnOuterPrefix.nested (guardedFrame frame p) base.toArray.size code) callers ValueReturnOuterPrefix.tail))
      (123 * op + fee cfg s p + rest) post := tail
  have result := prefixRule prefixNext
  have fuelEq : fuel + 82 + 77 = fuel + 159 := by omega
  have gasEq : 114 * op + (123 * op + fee cfg s p + rest) = budget cfg s p + rest := by dsimp [op, budget]; omega
  exact cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fuelEq gasEq rfl result

theorem epilogueAfter_credits (s : Store NearState) (op index rest : Nat) (scratch : UInt32)
    (hc : s.host.gas.Credits (27 * op + rest)) : (epilogueAfter s op index scratch).host.gas.Credits rest := by
  have c1 : (paid s op 1).host.gas.Credits (22 * op + (4 * op + rest)) :=
    paid_credits s op 1 _ (hc.mono (by omega))
  have cc := checkAfter_credits (paid s op 1) op index (4 * op + rest) scratch c1
  have cf := paid_credits (checkAfter (paid s op 1) op index scratch) op 4 rest cc
  exact cf

theorem cleanupAfter_credits (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (scratch counter : UInt32) (memory : Memory) (hc : s.host.gas.Credits (69 * op + rest)) :
    (cleanupAfter s op globalIndex memoryIndex scratch counter memory).host.gas.Credits rest := by
  have c5 : (paid s op 5).host.gas.Credits (36 * op + (op + (27 * op + rest))) :=
    paid_credits s op 5 _ (hc.mono (by omega))
  have cr := releaseAfter_credits (paid s op 5) op memoryIndex (op + (27 * op + rest)) counter memory c5
  have cb := WNear.Proofs.StorePair.charged_credits (releaseAfter (paid s op 5) op memoryIndex counter memory) op (27 * op + rest) cr
  exact epilogueAfter_credits _ op globalIndex rest scratch cb

/-- Sufficient total credits leave the requested residual after the actual body. -/
theorem final_credits (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (p : Layout)
    (hr : Ready cfg extra s limits frame callers p)
    (hc : s.host.gas.Credits (budget cfg s p + rest)) :
    (finalStore cfg s p).host.gas.Credits rest := by
  have cp := phase_credits cfg extra rest s limits frame callers p hr hc
  exact cleanupAfter_credits (returned cfg s p) cfg.regularOpCost p.globalIndex p.memoryIndex rest (scratch p) (counter p) (lowMemory p) cp.c_returned

end WNear.Proofs.ValueReturnOuterBody
