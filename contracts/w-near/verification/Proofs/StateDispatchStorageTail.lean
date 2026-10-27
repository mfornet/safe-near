import Proofs.StateDispatchStorageState
import Proofs.StateDispatchStorageGas
import Proofs.StateReadStorageFrame
import Proofs.StateDispatchStorageArguments
import Proofs.StateDispatchStorageCleanupFrame
import Binary.StateDispatchStorage

/-! Concrete f459 storage dispatch, release and accepted return tail. -/
namespace WNear.Proofs.StateDispatchStorageTail
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
set_option maxRecDepth 16384

def arguments (s : Store NearState) (op : Nat) := paid s op 10
def argumentFrame (frame : CallFrame) (p : StateDispatchStorage.Layout) := {frame with locals := frame.locals.set! 0 (.i32 (StateDispatchStorage.selected p))}
def returned (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchStorage.Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  StateReadStorage.callAfter cfg (arguments s cfg.regularOpCost) p.mi ctx.trie (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value
def cleaned (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchStorage.Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  StateDispatchStorageCleanup.after (returned cfg s p ctx key value) cfg.regularOpCost p.memoryIndex (StateDispatchStorage.counter p) (StateDispatchStorage.lowMemory p)
def after (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchStorage.Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  StateDispatchStorageFinish.after (cleaned cfg s p ctx key value) cfg.regularOpCost p.globalIndex (StateDispatchStorage.scratch p)
def finalFrame (frame : CallFrame) (p : StateDispatchStorage.Layout) :=
  StateDispatchStorageFinish.finalFrame (StateDispatchStorageCleanup.finalFrame (argumentFrame frame p) 1) 1

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n) = fields s := by
  induction n with | zero => rfl | succ n ih => exact ih

private theorem code_paid (s : Store NearState) (op n : Nat) (p : StateDispatchStorage.Layout) (inst extra : Nat)
    (h : StateDispatchStorage.Code s p inst extra) : StateDispatchStorage.Code (paid s op n) p inst extra := by
  have hfields := fields_paid s op n
  have hf := congrArg (fun x => x.1) hfields
  have hm := congrArg (fun x => x.2.1) hfields
  have ht := congrArg (fun x => x.2.2.1) hfields
  simp only [fields] at hf hm ht
  exact h.transport s (paid s op n) p inst extra hf hm ht

/-- All actual post-nonnull f459 instructions, including both real host and
release calls, the branch, accepted f432, and SP restoration. -/
theorem wp_tail (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (p : StateDispatchStorage.Layout) (global : GlobalInst)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (key value : List UInt8) (post : Post)
    (hc : StateDispatchStorage.Code s p frame.inst extra)
    (h1 : frame.locals[1]? = some (.i32 p.input)) (h2 : frame.locals[2]? = some (.i32 (StateDispatchStorage.scratch p)))
    (h3 : frame.locals[3]? = some (.i64 0)) (hn : 5 ≤ frame.locals.size) (hm : s.mems[p.memoryIndex]? = some (StateDispatchStorage.lowMemory p))
    (hg : s.globals[p.globalIndex]? = some global) (hsp : global.value = .i32 (StateDispatchStorage.scratch p))
    (hcell : (StateDispatchStorage.selected p).toNat + 8 ≤ (StateDispatchStorage.lowMemory p).byteSize)
    (hinput : p.input.toNat + 8 ≤ (StateDispatchStorage.lowMemory p).byteSize)
    (hvtable : (StateDispatchStorage.vtable p).toNat + 192 ≤ (StateDispatchStorage.lowMemory p).byteSize)
    (hrecord : ((StateDispatchStorage.scratch p + 8) ||| 4).toNat + 4 ≤ (StateDispatchStorage.lowMemory p).byteSize)
    (hcounter : (StateDispatchStorage.counter p).toNat + 4 ≤ (StateDispatchStorage.lowMemory p).byteSize)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hr : StorageReadCalls.Ready ⟨StateDispatchStorage.lowMemory p,s.host⟩ ctx raw storage (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value)
    (hgas : s.host.gas.Credits (104 * cfg.regularOpCost + StateDispatchStorage.fee s p ctx key value + rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p ctx key value) limits
      (base.toArray.push (.i64 1)) (finalFrame frame p) callers suffix)) rest post) :
    WP cfg (fuel + 67) (.next (atCode s limits (base.toArray.push (.i32 (StateDispatchStorage.selected p)))
      (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue)
      callers (WNear.Binary.StateDispatchStorage.dispatch ++ WNear.Binary.StateDispatchStorage.cleanup)))
      (104 * cfg.regularOpCost + StateDispatchStorage.fee s p ctx key value + rest) post := by
  let op := cfg.regularOpCost
  let a := arguments s op
  let h := returned cfg s p ctx key value
  let c := cleaned cfg s p ctx key value
  let f := argumentFrame frame p
  let r : UInt64 := 1
  let ep := WNear.Binary.StateDispatchStorage.epilogue ++ suffix
  let nf := StateDispatchStorageCleanup.nested f base.toArray.size ep WNear.Binary.StateDispatchStorage.fallback
  have ca := paid_credits s op 10 (94 * op + StateDispatchStorage.fee s p ctx key value + rest) (hgas.mono (by dsimp [op]; omega))
  have hfee : StateDispatchStorage.fee a p ctx key value = StateDispatchStorage.fee s p ctx key value := by
    simpa only [a,arguments,StateDispatchStorage.fee] using StateReadStorage.cost_paid s op 10 (StateDispatchStorage.lowMemory p) ctx.trie (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value
  have chost : a.host.gas.Credits (17 * cfg.regularOpCost + StateDispatchStorage.fee a p ctx key value + (77 * op + rest)) := by
    rw [hfee]
    exact ca.mono (by dsimp [op]; omega)
  have hma : a.mems[p.memoryIndex]? = some (StateDispatchStorage.lowMemory p) := by simpa only [a,arguments,paid,chargedStore] using hm
  have hra := StateReadStorage.ready_paid s op 10 (StateDispatchStorage.lowMemory p) ctx raw storage (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value hr
  have chr : h.host.gas.Credits (77 * op + rest) := StateDispatchStorageGas.host_credits cfg a p.mi p.memoryIndex (StateDispatchStorage.lowMemory p)
    ctx raw storage (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value (77 * op + rest) hc.prefixCode.memoryIndex hma hra chost
  have cc : c.host.gas.Credits (34 * op + rest) := StateDispatchStorageGas.cleanup_credits h op p.memoryIndex (34 * op + rest)
    (StateDispatchStorage.counter p) (StateDispatchStorage.lowMemory p) (chr.mono (by omega))
  have ac := code_paid s op 10 p frame.inst extra hc
  have hostFields := StateReadStorage.callAfter_fields cfg a p.mi ctx.trie (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value
  have hcode : StateDispatchStorage.Code h p frame.inst extra := ac.transport a h p frame.inst extra hostFields.1 hostFields.2.1 hostFields.2.2.1
  have cleanFields := StateDispatchStorageCleanup.after_fields h op p.memoryIndex (StateDispatchStorage.counter p) (StateDispatchStorage.lowMemory p)
  have ccode : StateDispatchStorage.Code c p frame.inst extra := hcode.transport h c p frame.inst extra cleanFields.1 cleanFields.2.1 cleanFields.2.2.1
  have hmh : h.mems[p.memoryIndex]? = some (StateDispatchStorage.lowMemory p) := StateReadStorage.callAfter_memory cfg a p.mi ctx.trie
    (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value p.memoryIndex (StateDispatchStorage.lowMemory p) hc.prefixCode.memoryIndex hma
  have gha : a.globals[p.globalIndex]? = some global := by simpa only [a,arguments,paid,chargedStore] using hg
  have ghh : h.globals[p.globalIndex]? = some global := by
    have eqg : h.globals = a.globals := by simpa only [h,returned,a,arguments,op] using hostFields.2.2.2
    rw [eqg]; exact gha
  have ghc : c.globals[p.globalIndex]? = some global := by
    have eqg : c.globals = h.globals := by simpa only [c,cleaned,h,returned,op] using cleanFields.2.2.2
    rw [eqg]; exact ghh
  let cf := StateDispatchStorageCleanup.finalFrame f r
  have c2 : cf.locals[2]? = some (.i32 (StateDispatchStorage.scratch p)) := by
    simpa [cf,StateDispatchStorageCleanup.finalFrame,f,argumentFrame] using h2
  have c3 : cf.locals[3]? = some (.i64 0) := by simpa [cf,StateDispatchStorageCleanup.finalFrame,f,argumentFrame] using h3
  have c4 : cf.locals[4]? = some (.i64 r) := by simp [cf,StateDispatchStorageCleanup.finalFrame,f,argumentFrame,show 4 < frame.locals.size by omega]
  have cn : 4 ≤ cf.locals.size := by simpa [cf,StateDispatchStorageCleanup.finalFrame,f,argumentFrame] using (show 4 ≤ frame.locals.size by omega)
  have fn : WP cfg fuel (.next (atCode (StateDispatchStorageFinish.after c op p.globalIndex (StateDispatchStorage.scratch p)) limits
      (base.toArray.push (.i64 r)) (StateDispatchStorageFinish.finalFrame cf r) callers suffix)) rest post := by
    simpa only [after,finalFrame,c,cf,r,f,op] using hnext
  have finish := StateDispatchStorageFinish.wp_epilogue cfg fuel rest c limits base cf callers suffix p.mi p.globalIndex 432 global
    (StateDispatchStorage.scratch p) r post c2 c3 c4 cn ccode.prefixCode.module hc.prefixCode.globalIndex ghc hsp ccode.returnIndex ccode.returnFunction
    (by omega) cc fn
  have cleanupNext : WP cfg (fuel + 25) (.next (atCode c limits base.toArray cf callers ep)) (34 * op + rest) post := by
    simpa only [ep,StateDispatchStorageFinish.code,WNear.Binary.StateDispatchStorage.epilogue,op] using finish
  have f2 : f.locals[2]? = some (.i32 (StateDispatchStorage.scratch p)) := by simpa [f,argumentFrame] using h2
  have cleanup := StateDispatchStorageCleanup.wp_cleanup cfg (fuel + 25) (34 * op + rest) h limits base f callers ep WNear.Binary.StateDispatchStorage.fallback
    (StateDispatchStorage.scratch p) (StateDispatchStorage.counter p) r p.mi p.memoryIndex 431 672 (StateDispatchStorage.lowMemory p) post f2 hcode.prefixCode.module hc.prefixCode.memoryIndex hmh
    hcode.releaseIndex hcode.releaseFunction hcode.swapIndex hcode.swapFunction rfl hrecord hcounter hd (chr.mono (by dsimp [op]; omega)) cleanupNext
  have stackEq : (base ++ [Value.i64 r]).toArray = base.toArray.push (.i64 r) := by apply Array.toList_inj.mp; simp
  have hnHost : WP cfg (fuel + 51) (.next (atCode h limits (base ++ [Value.i64 r]).toArray nf callers WNear.Binary.StateDispatchStorage.cleanup)) (77 * op + rest) post := by
    simpa only [stackEq,nf,StateDispatchStorageCleanup.code,WNear.Binary.StateDispatchStorage.cleanup,Nat.add_assoc,Nat.reduceAdd,
      show 43 * cfg.regularOpCost + (34 * op + rest) = 77 * op + rest by dsimp [op]; omega] using cleanup
  have host := StateDispatchHosts.wp_storage cfg extra (fuel + 51) (77 * op + rest) a limits base nf callers WNear.Binary.StateDispatchStorage.cleanup p.mi 43 284 p.memoryIndex p.tableAddress p.table
    (StateDispatchStorage.element p) (StateDispatchStorage.lowMemory p) ctx raw storage (StateDispatchStorage.receiver p)
    (StateDispatchStorage.keyLen p) (StateDispatchStorage.keyPtr p) 0 key value post ac.prefixCode.module ac.hostIndex ac.hostFunction
    ac.prefixCode.memoryIndex hma ac.storageIndex ac.storageFunction ac.prefixCode.tableIndex ac.prefixCode.table ac.storageElement ac.storageType hra (by omega) chost hnHost
  have prepareNext : WP cfg (fuel + 57) (.next (atCode a limits
      ((base ++ [Value.i32 (StateDispatchStorage.receiver p),.i64 (StateDispatchStorage.keyLen p),.i64 (StateDispatchStorage.keyPtr p),.i64 0]).toArray.push (.i32 (StateDispatchStorage.element p))) nf callers
      (.call_indirect 6 0 :: WNear.Binary.StateDispatchStorage.cleanup))) (94 * op + StateDispatchStorage.fee s p ctx key value + rest) post := by
    change WP cfg (fuel + 51 + 6) _ (17 * cfg.regularOpCost + StateDispatchStorage.fee a p ctx key value + (77 * op + rest)) post at host
    simpa only [hfee,Nat.add_assoc,Nat.reduceAdd,
      show 17 * cfg.regularOpCost + (StateDispatchStorage.fee s p ctx key value + (77 * op + rest)) = 94 * op + (StateDispatchStorage.fee s p ctx key value + rest) by dsimp [op]; omega] using host
  have h1n : (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue).locals[1]? = some (.i32 p.input) := h1
  have args := StateDispatchStorageArguments.wp_arguments cfg (fuel + 57) (94 * op + StateDispatchStorage.fee s p ctx key value + rest) s limits base
    (StateDispatchPrefix.nested frame base.toArray.size suffix WNear.Binary.StateDispatchStorage.fallback WNear.Binary.StateDispatchStorage.epilogue) callers
    (.call_indirect 6 0 :: WNear.Binary.StateDispatchStorage.cleanup) (StateDispatchStorage.selected p) p.input p.mi p.memoryIndex (StateDispatchStorage.lowMemory p) post
    h1n (by simpa [StateDispatchPrefix.nested,emptyBlockFrame] using (show 0 < frame.locals.size by omega)) hc.prefixCode.module hc.prefixCode.memoryIndex hm hcell hinput hvtable
    (hgas.mono (by dsimp [op]; omega)) prepareNext
  simpa only [WNear.Binary.StateDispatchStorage.dispatch,StateDispatchStorageArguments.code,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 10 * cfg.regularOpCost + (94 * op + (StateDispatchStorage.fee s p ctx key value + rest)) = 104 * cfg.regularOpCost + (StateDispatchStorage.fee s p ctx key value + rest) by dsimp [op]; omega] using args

end WNear.Proofs.StateDispatchStorageTail
