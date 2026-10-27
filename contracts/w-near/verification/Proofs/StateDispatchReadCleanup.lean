import Proofs.StateDispatchStorageCleanup

/-! Actual f435 cleanup keeps the status/frame and uses the current host-written memory. -/
namespace WNear.Proofs.StateDispatchReadCleanup
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

abbrev nested := StateDispatchStorageCleanup.nested
def releaseBefore (s : Store NearState) (op : Nat) := paid s op 5
def released (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  ValueReturnOuter.releaseAfter (releaseBefore s op) op index counter memory
def after (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  paid (released s op index counter memory) op 1
def code : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.i32_const 4,.i32_binop .or,.call 431,.br 1]

theorem wp_argument (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot : Nat) (scratch : UInt32) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (stack.push (.i32 ((scratch + 8) ||| 4))) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get slot, .i32_const 8, .i32_binop .add, .i32_const 4, .i32_binop .or] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ slot (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 8 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ scratch 8 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 4 post
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_or cfg fuel rest (paid s cfg.regularOpCost 4) limits stack frame callers code (scratch + 8) 4 post
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

theorem wp_cleanup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (epilogue fallback : List Instr) (scratch counter : UInt32)
    (mi : ModuleInst) (index address swapAddress : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[3]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (ha : mi.funcAddrs[431]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.releaseFunction))
    (hsa : mi.funcAddrs[672]? = some swapAddress)
    (hsf : s.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcounter : readI32 memory ((scratch + 8) ||| 4).toNat = counter)
    (hrb : ((scratch + 8) ||| 4).toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (42 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index counter memory) limits base.toArray
      frame callers epilogue)) rest post) :
    WP cfg (fuel + 25) (.next (atCode s limits base.toArray
      (nested frame base.toArray.size epilogue fallback) callers code)) (42 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let nf := nested frame base.toArray.size epilogue fallback
  have cp : (releaseBefore s op).host.gas.Credits (36 * op + (op + rest)) := by
    simpa only [releaseBefore] using paid_credits s op 5 (36 * op + (op + rest)) (hc.mono (by dsimp [op]; omega))
  have cr : (released s op index counter memory).host.gas.Credits (op + rest) :=
    ValueReturnOuter.releaseAfter_credits (releaseBefore s op) op index (op + rest) counter memory cp
  have xn : WP cfg fuel (.next (atCode (chargedStore (released s op index counter memory) op) limits base.toArray frame callers epilogue)) rest post := by
    simpa only [after,op,paid] using hnext
  have exit := wp_br_two_blocks cfg fuel rest (released s op index counter memory) limits base.toArray frame callers epilogue fallback [] post cr xn
  have pn : WP cfg (fuel + 1) (.next (atCode (released s op index counter memory) limits base.toArray nf callers [.br 1])) (op + rest) post := exit
  have hm5 : (releaseBefore s op).modules[frame.inst]? = some mi := by simpa only [releaseBefore,paid,chargedStore] using hm
  have hf5 : (releaseBefore s op).funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.releaseFunction) := by simpa only [releaseBefore,paid,chargedStore] using hf
  have hs5 : (releaseBefore s op).funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction) := by simpa only [releaseBefore,paid,chargedStore] using hsf
  have mem5 : (releaseBefore s op).mems[index]? = some memory := by simpa only [releaseBefore,paid,chargedStore] using hmem
  have call := ValueReturnOuter.wp_call_release cfg (fuel + 1) (op + rest) (releaseBefore s op) limits base nf callers
    [.br 1] ((scratch + 8) ||| 4) counter address frame.inst swapAddress frame.inst index mi mi mi memory post
    hm5 ha hf5 hm5 hi hsa hs5 hm5 hi mem5 hcounter hrb hcb hd cp (by simpa only [released,op] using pn)
  have stackEq : (base ++ [Value.i32 ((scratch + 8) ||| 4)]).toArray = base.toArray.push (.i32 ((scratch + 8) ||| 4)) := by apply Array.toList_inj.mp; simp
  have cn : WP cfg (fuel + 20) (.next (atCode (releaseBefore s op) limits (base.toArray.push (.i32 ((scratch + 8) ||| 4))) nf callers
      [.call 431,.br 1])) (37 * op + rest) post := by
    simpa only [stackEq,Nat.add_assoc,Nat.reduceAdd,
      show 36 * cfg.regularOpCost + (op + rest) = 37 * op + rest by dsimp [op]; omega] using call
  have hl' : nf.locals[3]? = some (.i32 scratch) := by simpa only [nf,nested,StateDispatchStorageCleanup.nested,emptyBlockFrame] using hl
  have arg := wp_argument cfg (fuel + 20) (37 * op + rest) s limits base.toArray nf callers
    [.call 431,.br 1] 3 scratch post hl' (hc.mono (by dsimp [op]; omega)) cn
  simpa only [code,releaseBefore,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5 * cfg.regularOpCost + (37 * op + rest) = 42 * cfg.regularOpCost + rest by dsimp [op]; omega] using arg

end WNear.Proofs.StateDispatchReadCleanup
