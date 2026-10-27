import Proofs.StateDispatchPrefixState
import Proofs.ValueReturnOuterPrefix

/-! Shared real SDK lookup/acquisition, parameterized by slot and diagnostics. -/
namespace WNear.Proofs.StateDispatchPrefix
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.ValueReturnOuter (wp_cell_guard wp_lookup_argument)
set_option maxRecDepth 16384
attribute [local irreducible] WP

theorem wp_acquire_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot : Nat) (scratch cell location : UInt32) (post : Post)
    (hs : frame.locals[slot]? = some (.i32 scratch)) (hc0 : frame.locals[0]? = some (.i32 cell))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (((stack.push (.i32 scratch)).push (.i32 cell)).push (.i32 location)) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get slot, .local_get 0, .i32_const location] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ slot (.i32 scratch) post hs (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 (.i32 cell) post hc0
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 2) limits _ frame callers code location post
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

private def codeFields (s : Store NearState) := (s.funcs, s.modules, s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : codeFields (paid s op n) = codeFields s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (cost : Nat) : codeFields (chargedStore s cost) = codeFields s := rfl
private theorem fields_global (s : Store NearState) (index : Nat) (value : Value) : codeFields (setGlobal s index value) = codeFields s := rfl
private theorem fields_lookup (s : Store NearState) (op : Nat) :
    codeFields (ValueReturnThreadLocal.indirectAfter s op) = codeFields s := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
    fields_paid, fields_charge]
private theorem phase_code (s t : Store NearState) (p : Layout) (inst : Nat)
    (h : Code s p inst) (hf : codeFields t = codeFields s) : Code t p inst := by
  exact h.transport s t p inst
    (congrArg (fun x => x.1) hf) (congrArg (fun x => x.2.1) hf) (congrArg (fun x => x.2.2) hf)


theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code tail fallback epilogue : List Instr) (p : Layout) (slot : Nat) (location : UInt32) (post : Post)
    (hr : Ready s limits frame callers p slot)
    (hc : s.host.gas.Credits (114 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (acquired s cfg.regularOpCost p) limits base.toArray
      (nested (guardedFrame frame p slot) base.toArray.size code fallback epilogue) callers tail)) rest post) :
    WP cfg (fuel + 77) (.next (atCode s limits base.toArray frame callers
      (body slot location tail fallback epilogue ++ code))) (114 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let fReserved := nested (reservedFrame frame p slot) base.toArray.size code fallback epilogue
  let fGuarded := nested (guardedFrame frame p slot) base.toArray.size code fallback epilogue
  have hdepth := hr.depth
  have hsize := hr.localSize
  have cr : (reserved s op p).host.gas.Credits (109 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have cl : (lookupBefore s op p).host.gas.Credits (107 * op + rest) := paid_credits (reserved s op p) op 2 _ (cr.mono (by omega))
  have ck : (looked s op p).host.gas.Credits (78 * op + rest) := ValueReturnThreadLocal.indirectAfter_credits (lookupBefore s op p) op _ (cl.mono (by omega))
  have cg : (paid (looked s op p) op 3).host.gas.Credits (75 * op + rest) := paid_credits (looked s op p) op 3 _ (ck.mono (by omega))
  have ca : (arguments s op p).host.gas.Credits (72 * op + rest) := paid_credits (paid (looked s op p) op 3) op 3 _ (cg.mono (by omega))
  have fieldsR : codeFields (reserved s op p) = codeFields s := by
    simp only [reserved, fields_global, fields_paid]
  have fieldsL : codeFields (lookupBefore s op p) = codeFields s := by
    simp only [lookupBefore, fields_paid, fieldsR]
  have fieldsA : codeFields (arguments s op p) = codeFields s := by
    simp only [arguments, fields_paid, looked, fields_lookup, fieldsL]
  have cR := phase_code s (reserved s op p) p frame.inst hr.code fieldsR
  have cL := phase_code s (lookupBefore s op p) p frame.inst hr.code fieldsL
  have cA := phase_code s (arguments s op p) p frame.inst hr.code fieldsA
  have cLF : Code (lookupBefore s op p) p fReserved.inst := by
    simpa only [fReserved, nested, emptyBlockFrame, reservedFrame] using cL
  have cAF : Code (arguments s op p) p fGuarded.inst := by
    simpa only [fGuarded, nested, emptyBlockFrame, guardedFrame, reservedFrame] using cA
  have hmemR : (reserved s op p).mems[p.memoryIndex]? = some p.memory := by
    simpa only [reserved, setGlobal, paid, chargedStore] using hr.memory
  have hmemL : (lookupBefore s op p).mems[p.memoryIndex]? = some p.memory := by
    simpa only [lookupBefore, paid, chargedStore] using hmemR
  have hmemA : (arguments s op p).mems[p.memoryIndex]? = some p.memory := by
    simpa only [arguments, looked, ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
      ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
      paid, chargedStore] using hmemL
  have hglobalA : (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    rw [arguments_globals]
    exact reserved_global s op p hr.global
  have hlocalCell : fGuarded.locals[0]? = some (.i32 1074904) := by
    simp [fGuarded, nested, emptyBlockFrame, guardedFrame, reservedFrame,
      show 0 < frame.locals.size from (Array.getElem?_eq_some_iff.mp hr.interfaceLocal).1]
  have hlocalScratch : fGuarded.locals[slot]? = some (.i32 (scratch p)) := by
    simp [fGuarded, nested, emptyBlockFrame, guardedFrame, reservedFrame,Ne.symm hr.slotNe,
      hr.localSize]
  have hinterface : fReserved.locals[0]? = some (.i32 p.interface) := by
    simpa [fReserved,nested,emptyBlockFrame,reservedFrame,hr.slotNe] using hr.interfaceLocal
  have callRule := ValueReturnAcquire.wp_call_acquire cfg fuel rest (arguments s op p) limits base fGuarded callers tail
    (scratch p) (scratch p) 1074904 location p.mi 429 p.globalIndex p.memoryIndex
    {p.global with value := .i32 (scratch p)} p.memory post cAF.acquireLinks cAF.acquireIndex cAF.acquireFunction
    cAF.globalIndex hglobalA rfl cAF.memoryIndex hmemA hr.memoryWf hr.cellBound hr.acquireOutBound hr.countAccepted (by decide)
    (by omega) ca
  have acquiredNext : WP cfg fuel (.next (atCode
      (ValueReturnAcquire.calledAcquireStore (arguments s op p) op p.globalIndex p.memoryIndex
        (scratch p) (scratch p) 1074904 p.memory) limits base.toArray fGuarded callers tail)) rest post := by
    simpa only [acquired, fGuarded, op] using hnext
  have called := callRule acquiredNext
  have argsRule := wp_acquire_arguments cfg (fuel + 47) (72 * op + rest) (paid (looked s op p) op 3) limits base.toArray
    fGuarded callers (.call 429 :: tail) slot (scratch p) 1074904 location post hlocalScratch hlocalCell (cg.mono (by omega))
  have argsStack : (base ++ [Value.i32 (scratch p), .i32 1074904, .i32 location]).toArray =
      (((base.toArray.push (.i32 (scratch p))).push (.i32 1074904)).push (.i32 location)) := by
    apply Array.toList_inj.mp; simp
  have calledNext : WP cfg (fuel + 47) (.next (atCode (arguments s op p) limits
      (((base.toArray.push (.i32 (scratch p))).push (.i32 1074904)).push (.i32 location)) fGuarded callers
      (.call 429 :: tail))) (72 * op + rest) post := by
    simpa only [argsStack, op] using called
  have arged := argsRule calledNext
  let guardCode : List Instr := [.local_get slot, .local_get 0, .i32_const location, .call 429] ++ tail
  have guardRule := wp_cell_guard cfg ((fuel + 47) + 3) (3 * op + (72 * op + rest)) (looked s op p) limits base.toArray
    fReserved callers guardCode 1074904 post (by decide) (ck.mono (by omega))
  have argsNext : WP cfg ((fuel + 47) + 3) (.next (atCode (paid (looked s op p) op 3) limits base.toArray
      {fReserved with locals := fReserved.locals.set! 0 (.i32 1074904)} callers guardCode)) (3 * op + (72 * op + rest)) post := by
    simpa only [guardCode, fReserved, fGuarded, nested, emptyBlockFrame, guardedFrame, reservedFrame,
      List.cons_append, List.nil_append, op] using arged
  have guarded := guardRule argsNext
  let lookupCode : List Instr := acquire slot location ++ tail
  have indirectRule := ValueReturnThreadLocal.wp_indirect_lookup cfg (((fuel + 47) + 3) + 3)
    (3 * op + (3 * op + (72 * op + rest))) (lookupBefore s op p) limits base fReserved callers lookupCode p.mi
    p.tableAddress 565 468 p.memoryIndex p.lookupElement p.table p.memory post cLF.module cLF.tableIndex cLF.table
    cLF.lookupElement cLF.lookupType cLF.lookupFunction cLF.helperIndex cLF.helperFunction cLF.memoryIndex hmemL
    hr.threadBound hr.threadStatus (by omega) (cl.mono (by omega))
  have singleStack : (base ++ [Value.i32 1074904]).toArray = base.toArray.push (.i32 1074904) := by
    apply Array.toList_inj.mp; simp
  have guardedNext : WP cfg (((fuel + 47) + 3) + 3) (.next (atCode (looked s op p) limits
      (base ++ [Value.i32 1074904]).toArray fReserved callers lookupCode))
      (3 * op + (3 * op + (72 * op + rest))) post := by
    simpa only [lookupCode, acquire, guardCode, List.cons_append, List.nil_append,
      singleStack, op] using guarded
  have indirected := indirectRule guardedNext
  have lookupRule := wp_lookup_argument cfg ((((fuel + 47) + 3) + 3) + 15)
    (29 * op + (3 * op + (3 * op + (72 * op + rest)))) (reserved s op p) limits base.toArray fReserved callers
    (.call_indirect 1 0 :: lookupCode) p.interface p.mi p.memoryIndex p.memory post hinterface
    (by simpa only [fReserved, nested, emptyBlockFrame, reservedFrame] using cR.module) cR.memoryIndex hmemR hr.interfaceBound
    (cr.mono (by omega))
  have lookupNext : WP cfg ((((fuel + 47) + 3) + 3) + 15) (.next (atCode (lookupBefore s op p) limits
      (base.toArray.push (.i32 (readI32 p.memory p.interface.toNat))) fReserved callers
      (.call_indirect 1 0 :: lookupCode))) (29 * op + (3 * op + (3 * op + (72 * op + rest)))) post := by
    simpa only [hr.interfaceRead] using indirected
  have head := lookupRule lookupNext
  rw [show ((((fuel + 47) + 3) + 3) + 15) + 2 = fuel + 70 by omega,
    show 2 * cfg.regularOpCost + (29 * op + (3 * op + (3 * op + (72 * op + rest)))) = 109 * op + rest by dsimp [op]; omega] at head
  have head' : WP cfg (fuel + 70) (.next (atCode (reserved s op p) limits base.toArray fReserved callers
      (inner slot location tail))) (109 * op + rest) post := by
    simpa only [inner, lookup, lookupCode,
      List.append_assoc, List.cons_append, List.nil_append] using head
  have innerRule := wp_block_empty cfg (fuel + 70) (109 * op + rest) (reserved s op p) limits base.toArray
    (emptyBlockFrame (reservedFrame frame p slot) base.toArray.size (epilogue ++ code))
    callers (inner slot location tail) fallback post cr
  have innered := innerRule head'
  have outerRule := wp_block_empty cfg ((fuel + 70) + 1) (109 * op + rest) (reserved s op p) limits base.toArray
    (reservedFrame frame p slot) callers ([.block .empty (inner slot location tail)] ++ fallback)
    (epilogue ++ code) post cr
  have outered := outerRule innered
  rw [show (fuel + 70 + 1) + 1 = fuel + 72 by omega] at outered
  have reserveRule := ValueReturnBorrow.wp_reserve cfg (fuel + 72) (109 * op + rest) s limits base.toArray frame callers
    (.block .empty ([.block .empty (inner slot location tail)] ++ fallback) ::
      (epilogue ++ code)) p.mi p.globalIndex p.global p.sp slot post
    hr.code.module hr.code.globalIndex hr.global hr.sp (hc.mono (by dsimp [op]; omega))
  have result := reserveRule outered
  rw [show fuel + 72 + 5 = fuel + 77 by omega,
    show 5 * cfg.regularOpCost + (109 * op + rest) = 114 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [body, prologue,
    WNear.Binary.ValueReturnBorrow.checkPrologue, List.append_assoc, List.cons_append, List.nil_append] using result


end WNear.Proofs.StateDispatchPrefix
