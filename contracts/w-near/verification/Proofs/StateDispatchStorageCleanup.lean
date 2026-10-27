import Proofs.ValueReturnOuter

/-! Actual f459 result save, release, and branch out of both accepted blocks. -/
namespace WNear.Proofs.StateDispatchStorageCleanup
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def nested (frame : CallFrame) (height : Nat) (epilogue fallback : List Instr) :=
  emptyBlockFrame (emptyBlockFrame frame height epilogue) height fallback
def finalFrame (frame : CallFrame) (value : UInt64) := {frame with locals := frame.locals.set! 4 (.i64 value)}
def releaseBefore (s : Store NearState) (op : Nat) := paid s op 6
def released (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  ValueReturnOuter.releaseAfter (releaseBefore s op) op index counter memory
def after (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  paid (released s op index counter memory) op 1

def code : Expr := [.local_set 4,.local_get 2,.i32_const 8,.i32_binop .add,.i32_const 4,.i32_binop .or,.call 431,.br 1]
attribute [local irreducible] releaseBefore released after

/-- Original current-memory bounds derive the real release counter access;
no post-release array lookup is supplied. -/
theorem wp_cleanup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (epilogue fallback : List Instr) (scratch counter : UInt32) (value : UInt64)
    (mi : ModuleInst) (index address swapAddress : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (ha : mi.funcAddrs[431]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.releaseFunction))
    (hsa : mi.funcAddrs[672]? = some swapAddress)
    (hsf : s.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcounter : readI32 memory ((scratch + 8) ||| 4).toNat = counter)
    (hrb : ((scratch + 8) ||| 4).toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (43 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index counter memory) limits base.toArray
      (finalFrame frame value) callers epilogue)) rest post) :
    WP cfg (fuel + 26) (.next (atCode s limits (base.toArray.push (.i64 value))
      (nested frame base.toArray.size epilogue fallback) callers code)) (43 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := {frame with locals := frame.locals.set! 4 (.i64 value)}
  let nf := nested f base.toArray.size epilogue fallback
  have cp : (releaseBefore s op).host.gas.Credits (36 * op + (op + rest)) := by
    simpa only [releaseBefore] using (paid_credits s op 6 (36 * op + (op + rest)) (hc.mono (by dsimp [op]; omega)))
  have cr : (released s op index counter memory).host.gas.Credits (op + rest) :=
    by simpa only [released] using (ValueReturnOuter.releaseAfter_credits (releaseBefore s op) op index (op + rest) counter memory cp)
  have xn : WP cfg fuel (.next (atCode (chargedStore (released s op index counter memory) op) limits base.toArray f callers epilogue)) rest post := by
    simpa only [after,finalFrame,f,op,paid] using hnext
  have exit := wp_br_two_blocks cfg fuel rest (released s op index counter memory) limits base.toArray f callers epilogue fallback [] post cr xn
  have pn : WP cfg (fuel + 1) (.next (atCode (released s op index counter memory) limits base.toArray nf callers [.br 1])) (op + rest) post := exit
  have hm6 : (releaseBefore s op).modules[frame.inst]? = some mi := by simpa only [releaseBefore,paid,chargedStore] using hm
  have hf6 : (releaseBefore s op).funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.releaseFunction) := by simpa only [releaseBefore,paid,chargedStore] using hf
  have hs6 : (releaseBefore s op).funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction) := by simpa only [releaseBefore,paid,chargedStore] using hsf
  have mem6 : (releaseBefore s op).mems[index]? = some memory := by simpa only [releaseBefore,paid,chargedStore] using hmem
  have call := ValueReturnOuter.wp_call_release cfg (fuel + 1) (op + rest) (releaseBefore s op) limits base nf callers
    [.br 1] ((scratch + 8) ||| 4) counter address frame.inst swapAddress frame.inst index mi mi mi memory post
    hm6 ha hf6 hm6 hi hsa hs6 hm6 hi mem6 hcounter hrb hcb hd cp (by simpa only [released,op] using pn)
  have stackEq : (base ++ [Value.i32 ((scratch + 8) ||| 4)]).toArray = base.toArray.push (.i32 ((scratch + 8) ||| 4)) := by apply Array.toList_inj.mp; simp
  have cn : WP cfg (fuel + 20) (.next (atCode (releaseBefore s op) limits (base.toArray.push (.i32 ((scratch + 8) ||| 4))) nf callers
      [.call 431,.br 1])) (37 * op + rest) post := by
    simpa only [stackEq,Nat.add_assoc,Nat.reduceAdd,
      show 36 * cfg.regularOpCost + (op + rest) = 37 * op + rest by dsimp [op]; omega] using call
  have hl' : nf.locals[2]? = some (.i32 scratch) := by simpa [nf,nested,emptyBlockFrame,f] using hl
  have arg := ValueReturnOuter.wp_cleanup_argument cfg (fuel + 20) (37 * op + rest) (paid s op 1) limits base.toArray nf callers
    [.call 431,.br 1] scratch post hl' (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) (by simpa only [releaseBefore,ValueReturnBorrow.paid_add,op] using cn)
  have an : WP cfg (fuel + 25) (.next (atCode (paid s op 1) limits base.toArray
      {(nested frame base.toArray.size epilogue fallback) with locals := (nested frame base.toArray.size epilogue fallback).locals.set! 4 (.i64 value)} callers
      [.local_get 2,.i32_const 8,.i32_binop .add,.i32_const 4,.i32_binop .or,.call 431,.br 1])) (42 * op + rest) post := by
    simpa only [releaseBefore,ValueReturnBorrow.paid_add,nf,nested,emptyBlockFrame,f,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 5 * cfg.regularOpCost + (37 * op + rest) = 42 * op + rest by dsimp [op]; omega] using arg
  have first := wp_local_set cfg (fuel + 25) (42 * op + rest) s limits base.toArray (nested frame base.toArray.size epilogue fallback) callers
    [.local_get 2,.i32_const 8,.i32_binop .add,.i32_const 4,.i32_binop .or,.call 431,.br 1] 4 (.i64 value) post
    (hc.mono (by dsimp [op]; omega)) an
  simpa only [code,show cfg.regularOpCost + (42 * op + rest) = 43 * cfg.regularOpCost + rest by dsimp [op]; omega] using first
end WNear.Proofs.StateDispatchStorageCleanup
