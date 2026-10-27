import Proofs.InterfaceSetState
import Proofs.InterfaceBorrowState
import Proofs.InterfaceStack

/-! Actual setter release, zero-status branch and 32-byte stack restoration. -/
namespace WNear.Proofs.InterfaceSetReleaseTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

theorem wp_release_argument (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (post : Post)
    (hl : frame.locals[3]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (stack.push (.i32 ((scratch + 24) ||| 4))) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get 3, .i32_const 24, .i32_binop .add, .i32_const 4, .i32_binop .or] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ 3 (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 24 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ scratch 24 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 4 post
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_or cfg fuel rest (paid s cfg.regularOpCost 4) limits stack frame callers code (scratch + 24) 4 post
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

def epilogueAfter (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  setGlobal (paid (ValueReturnOuter.checkAfter (paid s op 1) op index scratch) op 4) index (.i32 (scratch + 32))

def finalFrame (frame : CallFrame) := {frame with locals := frame.locals.set! 1 (.i32 0)}
def released (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  InterfaceBorrow.calledReleaseStore (paid s op 5) op index counter memory

def after (s : Store NearState) (op globalIndex memoryIndex : Nat) (scratch counter : UInt32) (memory : Memory) :=
  epilogueAfter (chargedStore (paid (released s op memoryIndex counter memory) op 2) op) op globalIndex scratch

private theorem charged_globals (s : Store NearState) (cost : Nat) :
    (chargedStore s cost).globals = s.globals := rfl

private theorem check_globals (s : Store NearState) (op index : Nat) (sp : UInt32) (global : GlobalInst)
    (hg : s.globals[index]? = some global) (hv : global.value = .i32 sp) :
    (ValueReturnOuter.checkAfter s op index sp).globals = s.globals := by
  have he : (ValueReturnOuter.nonnullEntry s op).globals = s.globals := by
    rw [ValueReturnOuter.nonnullEntry, charged_globals, charged_globals]
  have hg' : (ValueReturnOuter.nonnullEntry s op).globals[index]? = some global := by rw [he]; exact hg
  have hc := ValueReturnBorrow.checkedStore_globals (ValueReturnOuter.nonnullEntry s op) op index sp global hg' hv
  rw [ValueReturnOuter.checkAfter, hc, he]

/-- The real setter epilogue checks its reset status and restores scratch+32. -/
theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (global : GlobalInst) (post : Post)
    (hstatus : frame.locals[1]? = some (.i32 0)) (hspLocal : frame.locals[3]? = some (.i32 (scratch p)))
    (hcode : Code s p frame.inst) (hg : s.globals[p.globalIndex]? = some global)
    (hv : global.value = .i32 (scratch p)) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (epilogueAfter s cfg.regularOpCost p.globalIndex (scratch p))
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 20) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.epilogue ++ code))) (27 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let arg := paid s op 1
  unfold epilogueAfter at hnext
  generalize hchecked : ValueReturnOuter.checkAfter arg op p.globalIndex (scratch p) = checked at hnext
  have carg : arg.host.gas.Credits (22 * op + (4 * op + rest)) := paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  have cchecked := ValueReturnOuter.checkAfter_credits arg op p.globalIndex _ (scratch p) carg
  rw [hchecked] at cchecked
  have hmarg : arg.modules[frame.inst]? = some p.mi := by simpa only [arg, paid, chargedStore] using hcode.module
  have hfarg : arg.funcs[433]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.checkFunction) := by
    simpa only [arg, paid, chargedStore] using hcode.checkFunction
  have hgarg : arg.globals[p.globalIndex]? = some global := by simpa only [arg, paid, chargedStore] using hg
  have hmchecked : checked.modules[frame.inst]? = some p.mi := by
    rw [← hchecked]
    simpa only [ValueReturnOuter.checkAfter, ValueReturnOuter.nonnullEntry, ValueReturnBorrow.checkedStore, paid, chargedStore, setGlobal] using hmarg
  have hglobals : checked.globals = arg.globals := by
    rw [← hchecked]
    exact check_globals arg op p.globalIndex (scratch p) global hgarg hv
  have hgchecked : checked.globals[p.globalIndex]? = some global := by rw [hglobals]; exact hgarg
  have restoreNext : WP cfg fuel (.next (atCode
      (setGlobal (paid checked cfg.regularOpCost 4) p.globalIndex (.i32 (scratch p + 32)))
      limits base.toArray frame callers code)) rest post := by
    simpa only [op] using hnext
  have hrestore := InterfaceStack.wp_restore cfg fuel rest checked limits base.toArray frame callers code p.mi
    p.globalIndex global (scratch p) 3 32 post hspLocal hmchecked hcode.globalIndex hgchecked cchecked restoreNext
  have callRule := ValueReturnOuter.wp_call_check cfg (fuel + 4) (4 * op + rest) arg limits base frame callers
    ([.local_get 3, .i32_const 32, .i32_binop .add, .global_set 0] ++ code)
    433 frame.inst p.globalIndex p.mi p.mi global (scratch p) post hmarg hcode.checkIndex hfarg hmarg
    hcode.globalIndex hgarg hv hd carg
  rw [hchecked] at callRule
  have callNext := callRule hrestore
  have hs : (base ++ [Value.i32 0]).toArray = base.toArray.push (.i32 0) := by
    apply Array.toList_inj.mp; simp
  rw [hs] at callNext
  have localNext : WP cfg ((fuel + 4) + 15) (.next (atCode (chargedStore s cfg.regularOpCost) limits
      (base.toArray.push (.i32 0)) frame callers
      (.call 433 :: [.local_get 3, .i32_const 32, .i32_binop .add, .global_set 0] ++ code)))
      (22 * op + (4 * op + rest)) post := by
    simpa only [arg, paid, op, List.cons_append, List.nil_append] using callNext
  rw [show 27 * cfg.regularOpCost + rest = cfg.regularOpCost + (22 * op + (4 * op + rest)) by dsimp [op]; omega]
  have getRule := wp_local_get cfg ((fuel + 4) + 15) (22 * op + (4 * op + rest)) s limits base.toArray frame callers
    (.call 433 :: [.local_get 3, .i32_const 32, .i32_binop .add, .global_set 0] ++ code) 1 (.i32 0) post
    hstatus (hc.mono (by dsimp [op]; omega))
  simp only [op, List.cons_append, List.nil_append] at getRule localNext
  have result := getRule localNext
  simpa only [WNear.Binary.InterfaceSet.epilogue, List.append, List.cons_append, List.nil_append,
    Nat.add_assoc, Nat.reduceAdd] using result

private theorem release_resources (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    {InterfaceBorrow.calledReleaseStore s op index counter memory with mems := s.mems, host := s.host} = s := by
  have h := InterfaceBorrow.releasedStore_resources (InterfaceBorrow.releaseEntryStore s op) op index counter memory
  have hh := congrArg (fun t : Store NearState => {t with host := s.host}) h
  simpa only [InterfaceBorrow.calledReleaseStore, InterfaceBorrow.releaseEntryStore, chargedStore] using hh

attribute [local irreducible] released

/-- Complete actual setter release suffix, including the two-block branch,
status reset, f433 and 32-byte shadow-stack restoration. -/
theorem wp_release_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (counter : UInt32) (memory : Memory) (global : GlobalInst) (post : Post)
    (hspLocal : frame.locals[3]? = some (.i32 (scratch p)))
    (hcode : Code s p frame.inst) (hg : s.globals[p.globalIndex]? = some global)
    (hv : global.value = .i32 (scratch p))
    (hmemory : s.mems[p.memoryIndex]? = some memory)
    (hcounter : readI32 memory (((scratch p + 24) ||| 4).toNat) = counter)
    (hrb : ((scratch p + 24) ||| 4).toNat + 4 ≤ memory.byteSize)
    (hcb : counter.toNat + 4 ≤ memory.byteSize) (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (71 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p.globalIndex p.memoryIndex (scratch p) counter memory)
      limits base.toArray (finalFrame frame) callers code)) rest post) :
    WP cfg (fuel + 47) (.next (atCode s limits base.toArray
      (nested frame base.toArray.size code) callers WNear.Binary.InterfaceSet.release))
      (71 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let arg := paid s op 5
  let rel := released s op p.memoryIndex counter memory
  let branchStore := paid rel op 2
  let branched := chargedStore branchStore op
  let nf := nested frame base.toArray.size code
  let ff := finalFrame frame
  have carg : arg.host.gas.Credits (36 * op + (30 * op + rest)) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have crel : rel.host.gas.Credits (30 * op + rest) := by
    simpa only [rel, released, arg] using InterfaceBorrow.calledReleaseStore_credits arg op p.memoryIndex _ counter memory carg
  have cstatus : branchStore.host.gas.Credits (28 * op + rest) := paid_credits rel op 2 _ (crel.mono (by omega))
  have cbranch : branched.host.gas.Credits (27 * op + rest) := StorePair.charged_credits branchStore op _ (cstatus.mono (by omega))
  have hr := release_resources arg op p.memoryIndex counter memory
  have hf0 := congrArg (fun t : Store NearState => t.funcs) hr
  have hm0 := congrArg (fun t : Store NearState => t.modules) hr
  have ht0 := congrArg (fun t : Store NearState => t.tables) hr
  have hg0 := congrArg (fun t : Store NearState => t.globals) hr
  have hf : branched.funcs = s.funcs := by simpa only [branched, branchStore, rel, released, arg, paid, chargedStore] using hf0
  have hm : branched.modules = s.modules := by simpa only [branched, branchStore, rel, released, arg, paid, chargedStore] using hm0
  have ht : branched.tables = s.tables := by simpa only [branched, branchStore, rel, released, arg, paid, chargedStore] using ht0
  have hglobals : branched.globals = s.globals := by simpa only [branched, branchStore, rel, released, arg, paid, chargedStore] using hg0
  have cB : Code branched p ff.inst := by
    have h := hcode.transport s branched p frame.inst hf hm ht
    simpa only [ff, finalFrame] using h
  have hgb : branched.globals[p.globalIndex]? = some global := by rw [hglobals]; exact hg
  have hsize : 1 < frame.locals.size := by have h := (Array.getElem?_eq_some_iff.mp hspLocal).1; omega
  have hstatus : ff.locals[1]? = some (.i32 0) := by simp [ff, finalFrame, hsize]
  have hscratch : ff.locals[3]? = some (.i32 (scratch p)) := by simpa [ff, finalFrame] using hspLocal
  have nextB : WP cfg fuel (.next (atCode (epilogueAfter branched op p.globalIndex (scratch p))
      limits base.toArray ff callers code)) rest post := by
    simpa only [after, branched, branchStore, rel, ff, op] using hnext
  have ep := wp_epilogue cfg fuel rest branched limits base ff callers code p global post
    hstatus hscratch cB hgb hv (by omega) cbranch nextB
  have branch := wp_br_two_blocks cfg (fuel + 20) (27 * op + rest) branchStore limits base.toArray ff callers
    (WNear.Binary.InterfaceSet.epilogue ++ code) WNear.Binary.InterfaceSet.fallback [] post (cstatus.mono (by dsimp [op]; omega)) ep
  rw [show cfg.regularOpCost + (27 * op + rest) = 28 * op + rest by dsimp [op]; omega] at branch
  have statusNext : WP cfg ((fuel + 20) + 1) (.next (atCode (paid rel op 2) limits base.toArray
      {nf with locals := nf.locals.set! 1 (.i32 0)} callers [.br 1])) (28 * op + rest) post := by
    simpa only [branchStore, nf, ff, nested, finalFrame, emptyBlockFrame] using branch
  have setRule := wp_local_set cfg ((fuel + 20) + 1) (28 * op + rest) (paid rel op 1) limits base.toArray nf callers
    [.br 1] 1 (.i32 0) post (paid_credits rel op 1 _ (crel.mono (by omega)))
  have setNext := setRule statusNext
  have constRule := wp_i32_const cfg (((fuel + 20) + 1) + 1) (op + (28 * op + rest)) rel limits base.toArray nf callers
    [.local_set 1, .br 1] 0 post (crel.mono (by omega))
  have status := constRule setNext
  rw [show cfg.regularOpCost + (op + (28 * op + rest)) = 30 * op + rest by dsimp [op]; omega] at status
  have hmarg : arg.modules[nf.inst]? = some p.mi := by simpa only [arg, paid, chargedStore, nf, nested, emptyBlockFrame] using hcode.module
  have hrarg : arg.funcs[442]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.InterfaceBorrow.releaseFunction) := by
    simpa only [arg, paid, chargedStore] using hcode.releaseFunction
  have hsarg : arg.funcs[672]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction) := by
    simpa only [arg, paid, chargedStore] using hcode.swapFunction
  have hmemarg : arg.mems[p.memoryIndex]? = some memory := by simpa only [arg, paid, chargedStore] using hmemory
  have releaseRule := InterfaceBorrow.wp_call_release cfg ((((fuel + 20) + 1) + 1) + 1) (30 * op + rest)
    arg limits base nf callers [.i32_const 0, .local_set 1, .br 1] ((scratch p + 24) ||| 4) counter
    442 frame.inst 672 frame.inst p.memoryIndex p.mi p.mi p.mi memory post hmarg hcode.releaseIndex hrarg
    (by simpa only [arg, paid, chargedStore] using hcode.module) hcode.memoryIndex hcode.swapIndex hsarg
    (by simpa only [arg, paid, chargedStore] using hcode.module) hcode.memoryIndex hmemarg hcounter hrb hcb hd carg
  have releaseNext : WP cfg ((((fuel + 20) + 1) + 1) + 1) (.next (atCode
      (InterfaceBorrow.calledReleaseStore arg op p.memoryIndex counter memory) limits base.toArray nf callers
      [.i32_const 0, .local_set 1, .br 1])) (30 * op + rest) post := by
    simpa only [rel, released, arg, op, Nat.add_assoc, Nat.reduceAdd] using status
  have called := releaseRule releaseNext
  have ha : (base ++ [Value.i32 ((scratch p + 24) ||| 4)]).toArray = base.toArray.push (.i32 ((scratch p + 24) ||| 4)) := by
    apply Array.toList_inj.mp; simp
  rw [ha] at called
  have argsRule := wp_release_argument cfg (((((fuel + 20) + 1) + 1) + 1) + 19) (36 * op + (30 * op + rest)) s limits base.toArray nf callers
    [.call 442, .i32_const 0, .local_set 1, .br 1] (scratch p) post hspLocal (hc.mono (by dsimp [op]; omega))
  have argsNext : WP cfg (((((fuel + 20) + 1) + 1) + 1) + 19) (.next (atCode (paid s op 5) limits
      (base.toArray.push (.i32 ((scratch p + 24) ||| 4))) nf callers [.call 442, .i32_const 0, .local_set 1, .br 1]))
      (36 * op + (30 * op + rest)) post := by simpa only [arg, op] using called
  have result := argsRule argsNext
  rw [show 5 * cfg.regularOpCost + (36 * op + (30 * op + rest)) = 71 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.InterfaceSet.release, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd, nf, op]
    using result

end WNear.Proofs.InterfaceSetReleaseTail
