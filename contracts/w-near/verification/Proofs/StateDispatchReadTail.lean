import Proofs.StateDispatchReadState
import Proofs.StateDispatchReadGas
import Proofs.StateReadRegisterFrame
import Proofs.StateDispatchReadArguments
import Proofs.StateDispatchReadCleanupFrame
import Binary.StateDispatchRead

/-! Concrete f435 read-register dispatch, release and accepted return tail. -/
namespace WNear.Proofs.StateDispatchReadTail
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
set_option maxRecDepth 16384

def arguments (s : Store NearState) (op : Nat) := paid s op 9
def argumentFrame (frame : CallFrame) (p : StateDispatchRead.Layout) := {frame with locals := frame.locals.set! 4 (.i32 (StateDispatchRead.selected p))}
def returned (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchRead.Layout) (bytes : List UInt8) :=
  StateReadRegister.readCallAfter cfg (arguments s cfg.regularOpCost) p.mi (StateDispatchRead.ptr p) bytes
def cleaned (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchRead.Layout) (bytes : List UInt8) :=
  StateDispatchReadCleanup.after (returned cfg s p bytes) cfg.regularOpCost p.memoryIndex (StateDispatchRead.counter p bytes) (StateDispatchRead.readMemory p bytes)
def after (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchRead.Layout) (bytes : List UInt8) :=
  StateDispatchReadFinish.after (cleaned cfg s p bytes) cfg.regularOpCost p.globalIndex (StateDispatchRead.scratch p)

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih

private theorem code_paid (s : Store NearState) (op n : Nat) (p : StateDispatchRead.Layout) (inst extra : Nat)
    (h : StateDispatchRead.Code s p inst extra) : StateDispatchRead.Code (paid s op n) p inst extra := by
  have hfields := fields_paid s op n
  have hf := congrArg (fun x => x.1) hfields
  have hm := congrArg (fun x => x.2.1) hfields
  have ht := congrArg (fun x => x.2.2.1) hfields
  simp only [fields] at hf hm ht
  exact h.transport s (paid s op n) p inst extra hf hm ht

/-- Actual f435 read-register dispatch, release and zero-status return. -/
theorem wp_tail (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (p : StateDispatchRead.Layout) (global : GlobalInst) (bytes : List UInt8) (post : Post)
    (hc : StateDispatchRead.Code s p frame.inst extra)
    (h1 : frame.locals[1]? = some (.i32 p.inputRegister)) (h2 : frame.locals[2]? = some (.i32 p.inputPointer))
    (h0 : frame.locals[0]? = some (.i32 0)) (h3 : frame.locals[3]? = some (.i32 (StateDispatchRead.scratch p)))
    (hn : 5 ≤ frame.locals.size) (hm : s.mems[p.memoryIndex]? = some (StateDispatchRead.lowMemory p))
    (hg : s.globals[p.globalIndex]? = some global) (hsp : global.value = .i32 (StateDispatchRead.scratch p))
    (hcell : (StateDispatchRead.selected p).toNat + 8 ≤ (StateDispatchRead.lowMemory p).byteSize)
    (hinput : p.inputRegister.toNat + 8 ≤ (StateDispatchRead.lowMemory p).byteSize)
    (hptr : p.inputPointer.toNat + 4 ≤ (StateDispatchRead.lowMemory p).byteSize)
    (hvtable : (StateDispatchRead.vtable p).toNat + 16 ≤ (StateDispatchRead.lowMemory p).byteSize)
    (hreg : s.host.registers (StateDispatchRead.register p).toNat = some bytes)
    (hpayload : (StateDispatchRead.ptr p).toNat + bytes.length ≤ (StateDispatchRead.lowMemory p).byteSize)
    (hrecord : ((StateDispatchRead.scratch p + 8) ||| 4).toNat + 4 ≤ (StateDispatchRead.readMemory p bytes).byteSize)
    (hcounter : (StateDispatchRead.counter p bytes).toNat + 4 ≤ (StateDispatchRead.readMemory p bytes).byteSize)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hgas : s.host.gas.Credits (93 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p bytes) limits base.toArray (argumentFrame frame p) callers suffix)) rest post) :
    WP cfg (fuel + 59) (.next (atCode s limits (base.toArray.push (.i32 (StateDispatchRead.selected p)))
      (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue)
      callers (WNear.Binary.StateDispatchRead.dispatch ++ WNear.Binary.StateDispatchRead.cleanup)))
      (93 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest) post := by
  let op := cfg.regularOpCost
  have b0 : 9 * op + (84 * op + RegisterRead.readCost s.host bytes.length + rest) ≤ 93 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest := by dsimp [op]; omega
  have b1 : 15 * op + RegisterRead.readCost s.host bytes.length + (69 * op + rest) ≤ 84 * op + RegisterRead.readCost s.host bytes.length + rest := by omega
  have b2 : 42 * op + (27 * op + rest) ≤ 69 * op + rest := by omega
  let a := arguments s op
  let h := returned cfg s p bytes
  let c := cleaned cfg s p bytes
  let f := argumentFrame frame p
  let ep := WNear.Binary.StateDispatchRead.epilogue ++ suffix
  let nf := StateDispatchReadCleanup.nested f base.toArray.size ep WNear.Binary.StateDispatchRead.fallback
  have ca := paid_credits s op 9 (84 * op + RegisterRead.readCost s.host bytes.length + rest) (hgas.mono b0)
  have fee : RegisterRead.readCost a.host bytes.length = RegisterRead.readCost s.host bytes.length := by simp only [a,arguments,RegisterRead.readCost,paid,chargedStore,chargeHost]
  have chost : a.host.gas.Credits (15 * cfg.regularOpCost + RegisterRead.readCost a.host bytes.length + (69 * op + rest)) := by rw [fee]; exact ca.mono b1
  have hma : a.mems[p.memoryIndex]? = some (StateDispatchRead.lowMemory p) := by simpa only [a,arguments,paid,chargedStore] using hm
  have chr := StateDispatchReadGas.host_credits cfg a p.mi (StateDispatchRead.ptr p) bytes (69 * op + rest) chost
  have cc := StateDispatchReadGas.cleanup_credits h op p.memoryIndex (27 * op + rest) (StateDispatchRead.counter p bytes) (StateDispatchRead.readMemory p bytes) (chr.mono b2)
  have ac := code_paid s op 9 p frame.inst extra hc
  have hostFields := StateReadRegister.readCallAfter_fields cfg a p.mi (StateDispatchRead.ptr p) bytes
  have hcode : StateDispatchRead.Code h p frame.inst extra := ac.transport a h p frame.inst extra hostFields.1 hostFields.2.1 hostFields.2.2.1
  have cleanFields := StateDispatchReadCleanup.after_fields h op p.memoryIndex (StateDispatchRead.counter p bytes) (StateDispatchRead.readMemory p bytes)
  have ccode : StateDispatchRead.Code c p frame.inst extra := hcode.transport h c p frame.inst extra cleanFields.1 cleanFields.2.1 cleanFields.2.2.1
  have hmh : h.mems[p.memoryIndex]? = some (StateDispatchRead.readMemory p bytes) :=
    StateReadRegister.readCallAfter_memory cfg a p.mi p.memoryIndex (StateDispatchRead.lowMemory p) (StateDispatchRead.ptr p) bytes hc.prefixCode.memoryIndex hma
  have gha : a.globals[p.globalIndex]? = some global := by simpa only [a,arguments,paid,chargedStore] using hg
  have ghh : h.globals[p.globalIndex]? = some global := by
    have e : h.globals = a.globals := by simpa only [h,returned,a,arguments,op] using hostFields.2.2.2
    rw [e]; exact gha
  have ghc : c.globals[p.globalIndex]? = some global := by
    have e : c.globals = h.globals := by simpa only [c,cleaned,h,returned,op] using cleanFields.2.2.2
    rw [e]; exact ghh
  have f0 : f.locals[0]? = some (.i32 0) := by simpa [f,argumentFrame] using h0
  have f3 : f.locals[3]? = some (.i32 (StateDispatchRead.scratch p)) := by simpa [f,argumentFrame] using h3
  have fn : WP cfg fuel (.next (atCode (StateDispatchReadFinish.after c op p.globalIndex (StateDispatchRead.scratch p)) limits base.toArray f callers suffix)) rest post := hnext
  have finish := StateDispatchReadFinish.wp_epilogue cfg fuel rest c limits base f callers suffix p.mi p.globalIndex 433 global (StateDispatchRead.scratch p) post
    f0 f3 ccode.prefixCode.module hc.prefixCode.globalIndex ghc hsp ccode.returnIndex ccode.returnFunction (by omega) cc fn
  have cleanupNext : WP cfg (fuel + 20) (.next (atCode c limits base.toArray f callers ep)) (27 * op + rest) post := by
    simpa only [ep,StateDispatchReadFinish.code,WNear.Binary.StateDispatchRead.epilogue,op] using finish
  have cleanup := StateDispatchReadCleanup.wp_cleanup cfg (fuel + 20) (27 * op + rest) h limits base f callers ep WNear.Binary.StateDispatchRead.fallback
    (StateDispatchRead.scratch p) (StateDispatchRead.counter p bytes) p.mi p.memoryIndex 431 672 (StateDispatchRead.readMemory p bytes) post f3 hcode.prefixCode.module hc.prefixCode.memoryIndex hmh
    hcode.releaseIndex hcode.releaseFunction hcode.swapIndex hcode.swapFunction rfl hrecord hcounter hd (chr.mono b2) cleanupNext
  have hostNext : WP cfg (fuel + 45) (.next (atCode h limits base.toArray nf callers WNear.Binary.StateDispatchRead.cleanup)) (69 * op + rest) post := by
    simpa only [nf,StateDispatchReadCleanup.code,WNear.Binary.StateDispatchRead.cleanup,Nat.add_assoc,Nat.reduceAdd,
      show 42 * cfg.regularOpCost + (27 * op + rest) = 69 * op + rest by dsimp [op]; omega] using cleanup
  have ar : a.host.registers (StateDispatchRead.register p).toNat = some bytes := by simpa only [a,arguments,paid,chargedStore,chargeHost] using hreg
  have host := StateDispatchHosts.wp_read cfg extra (fuel + 45) (69 * op + rest) a limits base nf callers WNear.Binary.StateDispatchRead.cleanup p.mi 0 240 p.memoryIndex p.tableAddress p.table
    (StateDispatchRead.element p) (StateDispatchRead.lowMemory p) (StateDispatchRead.receiver p) (StateDispatchRead.register p) (StateDispatchRead.ptr p) bytes post
    ac.prefixCode.module ac.hostIndex ac.hostFunction ac.prefixCode.memoryIndex hma ac.readIndex ac.readFunction ac.prefixCode.tableIndex ac.prefixCode.table ac.readElement ac.readType ar hpayload (by omega) chost hostNext
  have prepareNext : WP cfg (fuel + 50) (.next (atCode a limits
      ((base ++ [Value.i32 (StateDispatchRead.receiver p),.i64 (StateDispatchRead.register p),.i64 (StateDispatchRead.ptr p)]).toArray.push (.i32 (StateDispatchRead.element p))) nf callers
      (.call_indirect 4 0 :: WNear.Binary.StateDispatchRead.cleanup))) (84 * op + RegisterRead.readCost s.host bytes.length + rest) post := by
    simpa only [fee,Nat.add_assoc,Nat.reduceAdd,
      show 15 * cfg.regularOpCost + (RegisterRead.readCost s.host bytes.length + (69 * op + rest)) = 84 * op + (RegisterRead.readCost s.host bytes.length + rest) by dsimp [op]; omega] using host
  have h1n : (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue).locals[1]? = some (.i32 p.inputRegister) := h1
  have h2n : (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue).locals[2]? = some (.i32 p.inputPointer) := h2
  have args := StateDispatchReadArguments.wp_arguments cfg (fuel + 50) (84 * op + RegisterRead.readCost s.host bytes.length + rest) s limits base
    (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchRead.fallback WNear.Binary.StateDispatchRead.epilogue) callers
    (.call_indirect 4 0 :: WNear.Binary.StateDispatchRead.cleanup) (StateDispatchRead.selected p) p.inputRegister p.inputPointer p.mi p.memoryIndex (StateDispatchRead.lowMemory p) post
    h1n h2n (by simpa [StateDispatchPrefix.nested,emptyBlockFrame] using (show 4 < frame.locals.size by omega)) hc.prefixCode.module hc.prefixCode.memoryIndex hm hcell hinput hptr hvtable (hgas.mono b0) prepareNext
  simpa only [WNear.Binary.StateDispatchRead.dispatch,StateDispatchReadArguments.code,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 9 * cfg.regularOpCost + (84 * op + (RegisterRead.readCost s.host bytes.length + rest)) = 93 * cfg.regularOpCost + (RegisterRead.readCost s.host bytes.length + rest) by dsimp [op]; omega] using args
end WNear.Proofs.StateDispatchReadTail
