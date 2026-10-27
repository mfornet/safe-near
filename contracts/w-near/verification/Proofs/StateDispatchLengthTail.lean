import Proofs.StateDispatchLengthState
import Proofs.StateDispatchLengthGas
import Proofs.StateReadRegisterFrame
import Binary.StateDispatchLength

/-! Concrete f440 register-length dispatch, release and accepted return tail. -/
namespace WNear.Proofs.StateDispatchLengthTail
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
set_option maxRecDepth 16384

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_charge (s : Store NearState) (amount : Nat) : fields (chargedStore s amount) = fields s := rfl

private theorem fields_release (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    fields (ValueReturnBorrowCounters.releasedStore s op index counter memory) = fields s := by
  have h := congrArg fields (ValueReturnBorrowCounters.releasedStore_resources s op index counter memory)
  simpa only [fields] using h

 theorem cleanup_fields (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    (StateDispatchLengthCleanup.after s op index counter memory).funcs = s.funcs ∧
    (StateDispatchLengthCleanup.after s op index counter memory).modules = s.modules ∧
    (StateDispatchLengthCleanup.after s op index counter memory).tables = s.tables ∧
    (StateDispatchLengthCleanup.after s op index counter memory).globals = s.globals := by
  let t := ValueReturnOuter.nonnullEntry (StateDispatchLengthCleanup.releaseBefore s op) op
  have hr := fields_release t op index counter memory
  have ha : fields (StateDispatchLengthCleanup.after s op index counter memory) = fields s := by
    simp only [StateDispatchLengthCleanup.after,fields_paid,StateDispatchLengthCleanup.released,ValueReturnOuter.releaseAfter]
    rw [hr]
    simp only [t,ValueReturnOuter.nonnullEntry,fields_charge,StateDispatchLengthCleanup.releaseBefore,fields_paid]
  have h1 := congrArg (fun x => x.1) ha
  have h2 := congrArg (fun x => x.2.1) ha
  have h3 := congrArg (fun x => x.2.2.1) ha
  have h4 := congrArg (fun x => x.2.2.2) ha
  simp only [fields] at h1 h2 h3 h4
  exact ⟨h1,h2,h3,h4⟩

def arguments (s : Store NearState) (op : Nat) := paid s op 7
def value (s : Store NearState) (op : Nat) (p : StateDispatchLength.Layout) := StateReadRegister.lengthValue (arguments s op) (StateDispatchLength.register p)
def argumentFrame (frame : CallFrame) (p : StateDispatchLength.Layout) := {frame with locals := frame.locals.set! 0 (.i32 (StateDispatchLength.selected p))}
def returned (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchLength.Layout) := StateReadRegister.lengthCallAfter cfg (arguments s cfg.regularOpCost) p.mi
def cleaned (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchLength.Layout) :=
  StateDispatchLengthCleanup.after (returned cfg s p) cfg.regularOpCost p.memoryIndex (StateDispatchLength.counter p) (StateDispatchLength.lowMemory p)
def after (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchLength.Layout) := StateDispatchLengthFinish.after (cleaned cfg s p) cfg.regularOpCost p.globalIndex (StateDispatchLength.scratch p)
def finalFrame (frame : CallFrame) (p : StateDispatchLength.Layout) (result : UInt64) :=
  StateDispatchLengthFinish.finalFrame (StateDispatchLengthCleanup.finalFrame (argumentFrame frame p) result) result

private theorem code_paid (s : Store NearState) (op n : Nat) (p : StateDispatchLength.Layout) (inst extra : Nat)
    (h : StateDispatchLength.Code s p inst extra) : StateDispatchLength.Code (paid s op n) p inst extra := by
  have hfields := fields_paid s op n
  have hf := congrArg (fun x => x.1) hfields
  have hm := congrArg (fun x => x.2.1) hfields
  have ht := congrArg (fun x => x.2.2.1) hfields
  simp only [fields] at hf hm ht
  exact h.transport s (paid s op n) p inst extra hf hm ht

/-- All actual post-nonnull f440 instructions, including both real host and
release calls, the branch, accepted f432, and SP restoration. -/
theorem wp_tail (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (p : StateDispatchLength.Layout) (global : GlobalInst) (post : Post)
    (hc : StateDispatchLength.Code s p frame.inst extra)
    (h1 : frame.locals[1]? = some (.i32 p.input)) (h2 : frame.locals[2]? = some (.i32 (StateDispatchLength.scratch p)))
    (hn : 5 ≤ frame.locals.size) (hm : s.mems[p.memoryIndex]? = some (StateDispatchLength.lowMemory p))
    (hg : s.globals[p.globalIndex]? = some global) (hsp : global.value = .i32 (StateDispatchLength.scratch p))
    (hcell : (StateDispatchLength.selected p).toNat + 8 ≤ (StateDispatchLength.lowMemory p).byteSize)
    (hinput : p.input.toNat + 8 ≤ (StateDispatchLength.lowMemory p).byteSize)
    (hvtable : (StateDispatchLength.vtable p).toNat + 20 ≤ (StateDispatchLength.lowMemory p).byteSize)
    (hrecord : ((StateDispatchLength.scratch p + 8) ||| 4).toNat + 4 ≤ (StateDispatchLength.lowMemory p).byteSize)
    (hcounter : (StateDispatchLength.counter p).toNat + 4 ≤ (StateDispatchLength.lowMemory p).byteSize)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hgas : s.host.gas.Credits (99 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits
      (base.toArray.push (.i64 (value s cfg.regularOpCost p))) (finalFrame frame p (value s cfg.regularOpCost p)) callers suffix)) rest post) :
    WP cfg (fuel + 64) (.next (atCode s limits (base.toArray.push (.i32 (StateDispatchLength.selected p)))
      (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue)
      callers (WNear.Binary.StateDispatchLength.dispatch ++ WNear.Binary.StateDispatchLength.cleanup)))
      (99 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest) post := by
  let op := cfg.regularOpCost
  let a := arguments s op
  let h := returned cfg s p
  let c := cleaned cfg s p
  let f := argumentFrame frame p
  let r := value s op p
  let ep := WNear.Binary.StateDispatchLength.epilogue ++ suffix
  let nf := StateDispatchLengthCleanup.nested f base.toArray.size ep WNear.Binary.StateDispatchLength.fallback
  have ca := paid_credits s op 7 (92 * op + s.host.extCosts.cost "base" + rest) (hgas.mono (by dsimp [op]; omega))
  have chost : a.host.gas.Credits (13 * cfg.regularOpCost + a.host.extCosts.cost "base" + (79 * op + rest)) := by
    simpa only [a,arguments,paid,chargedStore,chargeHost,op] using (ca.mono (by dsimp [op]; omega))
  have chr : h.host.gas.Credits (79 * op + rest) := StateDispatchLengthGas.host_credits cfg a p.mi (79 * op + rest) chost
  have cc : c.host.gas.Credits (34 * op + rest) := StateDispatchLengthGas.cleanup_credits h op p.memoryIndex (34 * op + rest)
    (StateDispatchLength.counter p) (StateDispatchLength.lowMemory p) (chr.mono (by omega))
  have ac := code_paid s op 7 p frame.inst extra hc
  have hostFields := StateReadRegister.lengthCallAfter_fields cfg a p.mi
  have hcode : StateDispatchLength.Code h p frame.inst extra := ac.transport a h p frame.inst extra hostFields.1 hostFields.2.1 hostFields.2.2.1
  have cleanFields := cleanup_fields h op p.memoryIndex (StateDispatchLength.counter p) (StateDispatchLength.lowMemory p)
  have ccode : StateDispatchLength.Code c p frame.inst extra := hcode.transport h c p frame.inst extra cleanFields.1 cleanFields.2.1 cleanFields.2.2.1
  have hma : a.mems[p.memoryIndex]? = some (StateDispatchLength.lowMemory p) := by simpa only [a,arguments,paid,chargedStore] using hm
  have hmh : h.mems[p.memoryIndex]? = some (StateDispatchLength.lowMemory p) := StateReadRegister.lengthCallAfter_memory cfg a p.mi p.memoryIndex
    (StateDispatchLength.lowMemory p) hc.prefixCode.memoryIndex hma
  have gha : a.globals[p.globalIndex]? = some global := by simpa only [a,arguments,paid,chargedStore] using hg
  have ghh : h.globals[p.globalIndex]? = some global := by
    have eqg : h.globals = a.globals := by simpa only [h,returned,a,arguments,op] using hostFields.2.2.2
    rw [eqg]; exact gha
  have ghc : c.globals[p.globalIndex]? = some global := by
    have eqg : c.globals = h.globals := by simpa only [c,cleaned,h,returned,op] using cleanFields.2.2.2
    rw [eqg]; exact ghh
  let cf := StateDispatchLengthCleanup.finalFrame f r
  have c2 : cf.locals[2]? = some (.i32 (StateDispatchLength.scratch p)) := by
    simpa [cf,StateDispatchLengthCleanup.finalFrame,StateDispatchLengthCleanup.statusFrame,f,argumentFrame] using h2
  have c3 : cf.locals[3]? = some (.i64 r) := by simp [cf,StateDispatchLengthCleanup.finalFrame,StateDispatchLengthCleanup.statusFrame,f,argumentFrame,show 3 < frame.locals.size by omega]
  have c4 : cf.locals[4]? = some (.i64 0) := by simp [cf,StateDispatchLengthCleanup.finalFrame,StateDispatchLengthCleanup.statusFrame,f,argumentFrame,show 4 < frame.locals.size by omega]
  have cn : 4 ≤ cf.locals.size := by simpa [cf,StateDispatchLengthCleanup.finalFrame,StateDispatchLengthCleanup.statusFrame,f,argumentFrame] using (show 4 ≤ frame.locals.size by omega)
  have fn : WP cfg fuel (.next (atCode (StateDispatchLengthFinish.after c op p.globalIndex (StateDispatchLength.scratch p)) limits
      (base.toArray.push (.i64 r)) (StateDispatchLengthFinish.finalFrame cf r) callers suffix)) rest post := by
    simpa only [after,finalFrame,c,cf,r,f,op] using hnext
  have finish := StateDispatchLengthFinish.wp_epilogue cfg fuel rest c limits base cf callers suffix p.mi p.globalIndex 432 global
    (StateDispatchLength.scratch p) r post c2 c3 c4 cn ccode.prefixCode.module hc.prefixCode.globalIndex ghc hsp ccode.returnIndex ccode.returnFunction
    (by omega) cc fn
  have cleanupNext : WP cfg (fuel + 25) (.next (atCode c limits base.toArray cf callers ep)) (34 * op + rest) post := by
    simpa only [ep,StateDispatchLengthFinish.code,WNear.Binary.StateDispatchLength.epilogue,op] using finish
  have f2 : f.locals[2]? = some (.i32 (StateDispatchLength.scratch p)) := by simpa [f,argumentFrame] using h2
  have cleanup := StateDispatchLengthCleanup.wp_cleanup cfg (fuel + 25) (34 * op + rest) h limits base f callers ep WNear.Binary.StateDispatchLength.fallback
    (StateDispatchLength.scratch p) (StateDispatchLength.counter p) r p.mi p.memoryIndex 431 672 (StateDispatchLength.lowMemory p) post f2 hcode.prefixCode.module hc.prefixCode.memoryIndex hmh
    hcode.releaseIndex hcode.releaseFunction hcode.swapIndex hcode.swapFunction rfl hrecord hcounter hd (chr.mono (by dsimp [op]; omega)) cleanupNext
  have stackEq : (base ++ [Value.i64 r]).toArray = base.toArray.push (.i64 r) := by apply Array.toList_inj.mp; simp
  have hnHost : WP cfg (fuel + 53) (.next (atCode h limits (base ++ [Value.i64 r]).toArray nf callers WNear.Binary.StateDispatchLength.cleanup)) (79 * op + rest) post := by
    simpa only [stackEq,nf,StateDispatchLengthCleanup.code,WNear.Binary.StateDispatchLength.cleanup,Nat.add_assoc,Nat.reduceAdd,
      show 45 * cfg.regularOpCost + (34 * op + rest) = 79 * op + rest by dsimp [op]; omega] using cleanup
  have length := StateDispatchHosts.wp_length cfg extra (fuel + 53) (79 * op + rest) a limits base nf callers WNear.Binary.StateDispatchLength.cleanup p.mi 1 241 p.memoryIndex p.tableAddress p.table
    (StateDispatchLength.element p) (StateDispatchLength.lowMemory p) (StateDispatchLength.receiver p) (StateDispatchLength.register p) post ac.prefixCode.module ac.hostIndex ac.hostFunction
    ac.prefixCode.memoryIndex hma ac.lengthIndex ac.lengthFunction ac.prefixCode.tableIndex ac.prefixCode.table ac.lengthElement ac.lengthType (by omega) chost hnHost
  have prepareNext : WP cfg (fuel + 57) (.next (atCode a limits
      ((base ++ [Value.i32 (StateDispatchLength.receiver p),.i64 (StateDispatchLength.register p)]).toArray.push (.i32 (StateDispatchLength.element p))) nf callers
      (.call_indirect 7 0 :: WNear.Binary.StateDispatchLength.cleanup))) (92 * op + s.host.extCosts.cost "base" + rest) post := by
    have fee : a.host.extCosts = s.host.extCosts := by simp only [a,arguments,paid,chargedStore,chargeHost]
    simpa only [fee,Nat.add_assoc,Nat.reduceAdd,
      show 13 * cfg.regularOpCost + (s.host.extCosts.cost "base" + (79 * op + rest)) = 92 * op + (s.host.extCosts.cost "base" + rest) by dsimp [op]; omega] using length
  have h1n : (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue).locals[1]? = some (.i32 p.input) := h1
  have args := StateDispatchBorrow.wp_length_arguments cfg (fuel + 57) (92 * op + s.host.extCosts.cost "base" + rest) s limits base
    (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchLength.fallback WNear.Binary.StateDispatchLength.epilogue) callers
    (.call_indirect 7 0 :: WNear.Binary.StateDispatchLength.cleanup) (StateDispatchLength.selected p) p.input p.mi p.memoryIndex (StateDispatchLength.lowMemory p) post
    h1n (by simpa [StateDispatchPrefix.nested,emptyBlockFrame] using (show 0 < frame.locals.size by omega)) hc.prefixCode.module hc.prefixCode.memoryIndex hm hcell hinput hvtable
    (hgas.mono (by dsimp [op]; omega)) prepareNext
  simpa only [WNear.Binary.StateDispatchLength.dispatch,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 7 * cfg.regularOpCost + (92 * op + (s.host.extCosts.cost "base" + rest)) = 99 * cfg.regularOpCost + (s.host.extCosts.cost "base" + rest) by dsimp [op]; omega] using args

end WNear.Proofs.StateDispatchLengthTail
