import Proofs.StateDispatchLengthFinish

/-! Actual storage dispatcher epilogue: status3/value4, f432, and SP restore. -/
namespace WNear.Proofs.StateDispatchStorageFinish
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def code : Expr := [.local_get 3,.local_get 4,.call 432,.local_set 3,
  .local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3]
def returned (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  StateDispatchReturn.callAfter (paid s op 2) op index scratch
abbrev afterReturn := StateDispatchLengthFinish.afterReturn
def after (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  afterReturn (returned s op index scratch) op index scratch
abbrev finalFrame := StateDispatchLengthFinish.finalFrame

theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (mi : ModuleInst) (index address : Nat) (global : GlobalInst)
    (scratch : UInt32) (value : UInt64) (post : Post)
    (h2 : frame.locals[2]? = some (.i32 scratch)) (h3 : frame.locals[3]? = some (.i64 0))
    (h4 : frame.locals[4]? = some (.i64 value)) (hn : 4 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 scratch)
    (hfi : mi.funcAddrs[432]? = some address)
    (hfn : s.funcs[address]? = some (.wasm WNear.Binary.StateDispatch.returnSignature frame.inst WNear.Binary.StateDispatch.returnFunction))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (34 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index scratch) limits
      (base.toArray.push (.i64 value)) (finalFrame frame value) callers suffix)) rest post) :
    WP cfg (fuel + 25) (.next (atCode s limits base.toArray frame callers (code ++ suffix)))
      (34 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let t := returned s op index scratch
  let f := finalFrame frame value
  have c2 : (paid s op 2).host.gas.Credits (26 * op + (6 * op + rest)) := paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  have ct : t.host.gas.Credits (6 * op + rest) := StateDispatchReturn.callAfter_credits (paid s op 2) op index _ scratch c2
  have hmt : t.modules = s.modules := (StateDispatchReturn.callAfter_fields (paid s op 2) op index scratch).2.2.1
  have hgt : t.globals = s.globals := StateDispatchReturn.callAfter_globals (paid s op 2) op index scratch global hg hsp
  have hm' : t.modules[frame.inst]? = some mi := by rw [hmt]; exact hm
  have hg' : t.globals[index]? = some global := by rw [hgt]; exact hg
  have tn : WP cfg fuel (.next (atCode (afterReturn t op index scratch) limits
      (base.toArray.push (.i64 value)) (finalFrame frame value) callers suffix)) rest post := by
    simpa only [after,t,op] using hnext
  have set := StateDispatchLengthFinish.wp_after_return cfg fuel rest t limits base frame callers suffix mi index global scratch value post h2 hn hm' hi hg' ct tn
  have stackEq : (base ++ [Value.i64 value]).toArray = base.toArray.push (.i64 value) := by apply Array.toList_inj.mp; simp
  have nextCall : WP cfg (fuel + 6) (.next (atCode t limits (base ++ [Value.i64 value]).toArray frame callers
      (.local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix))) (6 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,stackEq,op] using set
  have call := StateDispatchReturn.wp_call cfg (fuel + 6) (6 * op + rest) (paid s op 2) limits base frame callers
    (.local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix)
    mi index address global scratch 0 value post hm hi hg hsp hfi hfn rfl hd c2 (by simpa only [t,returned,op,List.cons_append,List.nil_append] using nextCall)
  have stackArgs : (base ++ [Value.i64 0,.i64 value]).toArray = (base.toArray.push (.i64 0)).push (.i64 value) := by
    apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel + 23) (.next (atCode (paid s op 2) limits ((base.toArray.push (.i64 0)).push (.i64 value)) frame callers
      (.call 432 :: .local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix))) (32 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,stackArgs,Nat.add_assoc,Nat.reduceAdd,
      show 26 * cfg.regularOpCost + (6 * op + rest) = 32 * op + rest by dsimp [op]; omega] using call
  have getValue := wp_local_get cfg (fuel + 23) (32 * op + rest) (paid s op 1) limits (base.toArray.push (.i64 0)) frame callers
    (.call 432 :: .local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix) 4 (.i64 value) post h4
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) (by simpa only [op,paid,List.cons_append,List.nil_append] using callNext)
  have getStatus := wp_local_get cfg (fuel + 24) (op + (32 * op + rest)) s limits base.toArray frame callers
    (.local_get 4 :: .call 432 :: .local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix) 3 (.i64 0) post h3
    (hc.mono (by dsimp [op]; omega)) (by simpa only [op,paid,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using getValue)
  simpa only [code,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (32 * op + rest)) = 34 * cfg.regularOpCost + rest by dsimp [op]; omega] using getStatus
end WNear.Proofs.StateDispatchStorageFinish
