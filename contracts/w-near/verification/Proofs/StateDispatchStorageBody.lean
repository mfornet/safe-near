import Proofs.StateDispatchStorageFrame
import Proofs.StateDispatchStorageTail
import Proofs.StateDispatchStorageBorrow
import Proofs.StateDispatchStorageHost

/-! Complete actual initialized storage-read dispatcher f459. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 StateDispatchLength.acquired StateDispatchLength.high StateDispatchLength.low checked arguments returned
attribute [local irreducible] StateDispatchStorageBorrow.high StateDispatchStorageBorrow.low StateDispatchStorageBorrow.after
set_option maxRecDepth 16384

def finalStore (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  StateDispatchStorageTail.after cfg (checked s cfg.regularOpCost p) p ctx key value
def finalFrame (frame : CallFrame) (p : Layout) := StateDispatchStorageTail.finalFrame (copiedFrame frame p) p

private theorem borrow_credits (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) (rest : Nat)
    (hc : s.host.gas.Credits (30 * op + rest)) :
    (StateDispatchStorageBorrow.after s op index memory scratch).host.gas.Credits rest := by
  have b0 : 4 * op + (26 * op + rest) ≤ 30 * op + rest := by omega
  have b1 : 5 * op + (21 * op + rest) ≤ 26 * op + rest := by omega
  have b2 : 2 * op + (19 * op + rest) ≤ 21 * op + rest := by omega
  have b3 : 6 * op + (13 * op + rest) ≤ 19 * op + rest := by omega
  have ch : (StateDispatchStorageBorrow.high s op index memory scratch).host.gas.Credits (26 * op + rest) := by
    unfold StateDispatchStorageBorrow.high
    rw [storeI32_host]
    exact paid_credits s op 4 _ (hc.mono b0)
  have cl : (StateDispatchStorageBorrow.low s op index memory scratch).host.gas.Credits (21 * op + rest) := by
    unfold StateDispatchStorageBorrow.low
    rw [storeI32_host]
    exact paid_credits _ op 5 _ (ch.mono b1)
  have cs := paid_credits (StateDispatchStorageBorrow.low s op index memory scratch) op 2 (19 * op + rest) (cl.mono b2)
  unfold StateDispatchStorageBorrow.after
  exact ValueReturnOuter.nonnullAfter_credits (paid (paid (StateDispatchStorageBorrow.low s op index memory scratch) op 2) op 6) op rest
    (paid_credits _ op 6 (13 * op + rest) (cs.mono b3))

 theorem checked_fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) :
    fee (checked s cfg.regularOpCost p) p ctx key value = fee s p ctx key value :=
  cost_of_host_mask s.host (checked s cfg.regularOpCost p).host (lowMemory p) ctx.trie (keyLen p) (keyPtr p) 0 key value (checked_host s cfg.regularOpCost p)

 theorem checked_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) (rest : Nat)
    (hc : s.host.gas.Credits (248 * cfg.regularOpCost + fee s p ctx key value + rest)) :
    (checked s cfg.regularOpCost p).host.gas.Credits (104 * cfg.regularOpCost + fee (checked s cfg.regularOpCost p) p ctx key value + rest) := by
  let op := cfg.regularOpCost
  have b0 : 114 * op + (134 * op + fee s p ctx key value + rest) ≤ 248 * cfg.regularOpCost + fee s p ctx key value + rest := by dsimp [op]; omega
  have b1 : 30 * op + (104 * op + fee s p ctx key value + rest) ≤ 134 * op + fee s p ctx key value + rest := by omega
  have ca := (StateDispatchPrefix.acquired_gas s op (134 * op + fee s p ctx key value + rest) p.toLayout (hc.mono b0)).2.2
  rw [checked_fee,←borrow_after_eq]
  simpa only [acquired,StateDispatchLength.acquired,op] using borrow_credits (StateDispatchPrefix.acquired s op p.toLayout) op p.memoryIndex (acquiredMemory p) (scratch p) _ (ca.mono b1)

 theorem borrow_selected_eq (p : Layout) : StateDispatchStorageBorrow.selected (acquiredMemory p) (scratch p) = selected p := rfl
 theorem borrow_frame_eq (frame : CallFrame) (p : Layout) (height : Nat) (code : List Instr) :
    StateDispatchStorageBorrow.finalFrame
      (StateDispatchPrefix.nested (acquiredFrame frame p) height code WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue)
      (acquiredMemory p) (scratch p) =
    StateDispatchPrefix.nested (copiedFrame frame p) height code WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue := by
  simp only [StateDispatchStorageBorrow.finalFrame,StateDispatchStorageBorrow.copiedFrame,StateDispatchStorageBorrow.pointer,
    StateDispatchStorageBorrow.highMemory,StateDispatchPrefix.nested,emptyBlockFrame,copiedFrame,
    borrowed,StateDispatchLength.borrowed,StateDispatchLength.highMemory,scratch,StateDispatchLength.scratch]

/-- Full accepted f459 body: the original interface/counter/scratch resources
select real lookup, acquisition, host read, release and result return. -/
theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (p : Layout)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key value : List UInt8) (post : Post)
    (hr : Ready s limits frame callers p extra)
    (hcanonical : StorageReadCalls.Ready ⟨lowMemory p,s.host⟩ ctx raw storage (keyLen p) (keyPtr p) 0 key value)
    (hc : s.host.gas.Credits (248 * cfg.regularOpCost + fee s p ctx key value + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s p ctx key value) limits
      (base.toArray.push (.i64 1))
      (finalFrame frame p) callers suffix)) rest post) :
    WP cfg (fuel + 167) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDispatchStorage.body ++ suffix)))
      (248 * cfg.regularOpCost + fee s p ctx key value + rest) post := by
  let op := cfg.regularOpCost
  have hsize2 : 2 < frame.locals.size := by have := hr.localSize; omega
  have hsize0 : 0 < frame.locals.size := by have := hr.localSize; omega
  have d1 : callers.length + 1 < limits.maxCallDepth := by have := hr.prefixReady.depth; omega
  have d2 : callers.length + 2 < limits.maxCallDepth := by have := hr.prefixReady.depth; omega
  have cutPrefix : 114 * op + (134 * op + fee s p ctx key value + rest) ≤ 248 * cfg.regularOpCost + fee s p ctx key value + rest := by dsimp [op]; omega
  have cutBorrow : 30 * cfg.regularOpCost + (104 * op + fee s p ctx key value + rest) ≤ 134 * op + fee s p ctx key value + rest := by dsimp [op]; omega
  have eqBorrow : 30 * cfg.regularOpCost + (104 * op + (fee s p ctx key value + rest)) = 134 * op + (fee s p ctx key value + rest) := by dsimp [op]; omega
  have eqPrefix : 114 * cfg.regularOpCost + (134 * op + (fee s p ctx key value + rest)) = 248 * cfg.regularOpCost + (fee s p ctx key value + rest) := by dsimp [op]; omega
  have hchecked := hr.code.checked s op p frame.inst extra
  have gh := checked_global s op p hr.prefixReady.global
  have hs1 : (copiedFrame frame p).locals[1]? = some (.i32 p.input) := by
    simpa [copiedFrame,acquiredFrame,StateDispatchLength.acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.inputLocal
  have hs2 : (copiedFrame frame p).locals[2]? = some (.i32 (scratch p)) := by
    simp [copiedFrame,acquiredFrame,StateDispatchLength.acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,scratch,StateDispatchLength.scratch,hsize2]
  have hsSize : 5 ≤ (copiedFrame frame p).locals.size := by
    simpa [copiedFrame,acquiredFrame,StateDispatchLength.acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using hr.localSize
  have hs3 : (copiedFrame frame p).locals[3]? = some (.i64 0) := by
    simp [copiedFrame,acquiredFrame,StateDispatchLength.acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,show 3 < frame.locals.size by have := hr.localSize; omega]
  have canonicalChecked := ready_of_host_mask s.host (checked s op p).host (lowMemory p) ctx raw storage (keyLen p) (keyPtr p) 0 key value (checked_host s op p) hcanonical
  have tn : WP cfg fuel (.next (atCode (StateDispatchStorageTail.after cfg (checked s op p) p ctx key value) limits
      (base.toArray.push (.i64 1)) (StateDispatchStorageTail.finalFrame (copiedFrame frame p) p) callers suffix)) rest post := by
    simpa only [finalStore,finalFrame,op] using hnext
  have tail := StateDispatchStorageTail.wp_tail cfg extra fuel rest (checked s op p) limits base (copiedFrame frame p) callers suffix p {p.global with value := .i32 (scratch p)} ctx raw storage key value post
    hchecked hs1 hs2 hs3 hsSize (checked_memory s op p hr.prefixReady.memory) gh rfl hr.cellBound hr.inputBound hr.vtableBound hr.releaseBound hr.counterBound
    d2 canonicalChecked (checked_credits cfg s p ctx key value rest hc) tn
  let gf := StateDispatchPrefix.nested (acquiredFrame frame p) base.toArray.size suffix WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue
  have gaFields := StateDispatchPrefix.acquired_fields s op p.toLayout
  have gam : (acquired s op p).modules[gf.inst]? = some p.mi := by
    have eqm : (acquired s op p).modules = s.modules := by simpa only [acquired,StateDispatchLength.acquired] using gaFields.2.1
    rw [eqm]
    exact hr.code.prefixCode.module
  have gaf : (acquired s op p).funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.nonnullFunction) := by
    have eqf : (acquired s op p).funcs = s.funcs := by simpa only [acquired,StateDispatchLength.acquired] using gaFields.1
    rw [eqf]; exact hr.code.nonnullFunction
  have gamem : (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
    simpa only [acquired,StateDispatchLength.acquired,acquiredMemory,StateDispatchLength.acquiredMemory,scratch,StateDispatchLength.scratch,StateDispatchPrefix.acquiredMemory] using StateDispatchPrefix.acquired_memory s op p.toLayout hr.prefixReady.memory
  have gs : gf.locals[2]? = some (.i32 (scratch p)) := by
    simp [gf,StateDispatchPrefix.nested,emptyBlockFrame,acquiredFrame,StateDispatchLength.acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame,scratch,StateDispatchLength.scratch,
      hsize2]
  have ca : (acquired s op p).host.gas.Credits (134 * op + fee s p ctx key value + rest) := by
    unfold acquired
    simpa only [StateDispatchLength.acquired] using (StateDispatchPrefix.acquired_gas s op (134 * op + fee s p ctx key value + rest) p.toLayout (hc.mono cutPrefix)).2.2
  have bn : WP cfg (fuel + 67) (.next (atCode
      (StateDispatchStorageBorrow.after (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)) limits
      (base.toArray.push (.i32 (StateDispatchStorageBorrow.selected (acquiredMemory p) (scratch p))))
      (StateDispatchStorageBorrow.finalFrame gf (acquiredMemory p) (scratch p)) callers
      (WNear.Binary.StateDispatchStorage.dispatch ++ WNear.Binary.StateDispatchStorage.cleanup)))
      (104 * op + fee s p ctx key value + rest) post := by
    have feeEq := checked_fee cfg s p ctx key value
    simpa only [borrow_after_eq,borrow_selected_eq,gf,borrow_frame_eq,feeEq,op,Nat.add_assoc] using tail
  have borrow := StateDispatchStorageBorrow.wp_borrow cfg (fuel + 67) (104 * op + fee s p ctx key value + rest) (acquired s op p) limits base gf callers
    (WNear.Binary.StateDispatchStorage.dispatch ++ WNear.Binary.StateDispatchStorage.cleanup) p.mi p.memoryIndex 430 (acquiredMemory p) (scratch p) post gs (by simpa [gf,StateDispatchPrefix.nested,emptyBlockFrame,acquiredFrame,StateDispatchLength.acquiredFrame,StateDispatchPrefix.guardedFrame,StateDispatchPrefix.reservedFrame] using (show 4 ≤ frame.locals.size by have := hr.localSize; omega)) gam hr.code.prefixCode.memoryIndex gamem hr.code.nonnullIndex gaf
    hr.highBound hr.lowBound hr.selectBound hr.selectedNonzero d1 (ca.mono cutBorrow) bn
  have pn : WP cfg (fuel + 90) (.next (atCode (StateDispatchPrefix.acquired s op p.toLayout) limits base.toArray
      (StateDispatchPrefix.nested (StateDispatchPrefix.guardedFrame frame p.toLayout 2) base.toArray.size suffix
        WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue) callers WNear.Binary.StateDispatchStorage.tail))
      (134 * op + fee s p ctx key value + rest) post := by
    simpa only [WNear.Binary.StateDispatchStorage.tail,WNear.Binary.StateDispatchStorage.copyRecord,WNear.Binary.StateDispatchStorage.selectRecord,
      gf,acquiredFrame,StateDispatchLength.acquiredFrame,acquired,StateDispatchLength.acquired,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      eqBorrow] using borrow
  have head := StateDispatchPrefix.wp_prefix cfg (fuel + 90) (134 * op + fee s p ctx key value + rest) s limits base frame callers suffix
    WNear.Binary.StateDispatchStorage.tail WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue p.toLayout 2 1056340 post hr.prefixReady
    (hc.mono cutPrefix) pn
  simpa only [WNear.Binary.StateDispatchStorage.body,WNear.Binary.StateDispatchStorage.prologue,WNear.Binary.StateDispatchStorage.lookupAcquire,
    StateDispatchPrefix.body,StateDispatchPrefix.prologue,StateDispatchPrefix.inner,StateDispatchPrefix.lookup,StateDispatchPrefix.acquire,
    List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    eqPrefix] using head
end WNear.Proofs.StateDispatchStorage
