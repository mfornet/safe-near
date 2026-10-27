import Proofs.StateDispatchReturnFrame
import Proofs.InterfaceStack

/-! Actual f440 epilogue: accepted f432, SP restoration, and i64 result. -/
namespace WNear.Proofs.StateDispatchLengthFinish
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def code : Expr := [.local_get 4,.local_get 3,.call 432,.local_set 3,
  .local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3]
def returned (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  StateDispatchReturn.callAfter (paid s op 2) op index scratch
def afterReturn (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  paid (setGlobal (paid (paid s op 1) op 4) index (.i32 (scratch + 16))) op 1
def after (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  afterReturn (returned s op index scratch) op index scratch

def finalFrame (frame : CallFrame) (value : UInt64) := {frame with locals := frame.locals.set! 3 (.i64 value)}

theorem wp_after_return (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (mi : ModuleInst) (index : Nat) (global : GlobalInst)
    (scratch : UInt32) (value : UInt64) (post : Post)
    (h2 : frame.locals[2]? = some (.i32 scratch)) (hn : 4 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (afterReturn s cfg.regularOpCost index scratch) limits
      (base.toArray.push (.i64 value)) (finalFrame frame value) callers suffix)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits (base.toArray.push (.i64 value)) frame callers
      ([.local_set 3,.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix)))
      (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := finalFrame frame value
  have c1 := paid_credits s op 1 (5 * op + rest) (hc.mono (by dsimp [op]; omega))
  have c5 : (setGlobal (paid (paid s op 1) op 4) index (.i32 (scratch + 16))).host.gas.Credits (op + rest) :=
    paid_credits (paid s op 1) op 4 _ (c1.mono (by omega))
  have h3' : f.locals[3]? = some (.i64 value) := by simp [f,finalFrame,show 3 < frame.locals.size by omega]
  have h2' : f.locals[2]? = some (.i32 scratch) := by simpa [f,finalFrame] using h2
  have hm' : (paid s op 1).modules[f.inst]? = some mi := by simpa only [paid,chargedStore,f,finalFrame] using hm
  have hg' : (paid s op 1).globals[index]? = some global := hg
  have last := wp_local_get cfg fuel rest (setGlobal (paid (paid s op 1) op 4) index (.i32 (scratch + 16))) limits base.toArray f callers suffix
    3 (.i64 value) post h3' c5 hnext
  have restore := InterfaceStack.wp_restore cfg (fuel + 1) (op + rest) (paid s op 1) limits base.toArray f callers (.local_get 3 :: suffix)
    mi index global scratch 2 16 post h2' hm' hi hg' (c1.mono (by omega)) last
  have result := wp_local_set cfg (fuel + 5) (4 * cfg.regularOpCost + (op + rest)) s limits base.toArray frame callers
    ([.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix) 3 (.i64 value) post
    (hc.mono (by dsimp [op]; omega)) (by simpa only [f,finalFrame,op,paid,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using restore)
  simpa only [List.cons_append,List.nil_append,
    show cfg.regularOpCost + (4 * cfg.regularOpCost + (op + rest)) = 6 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (mi : ModuleInst) (index address : Nat) (global : GlobalInst)
    (scratch : UInt32) (value : UInt64) (post : Post)
    (h2 : frame.locals[2]? = some (.i32 scratch)) (h3 : frame.locals[3]? = some (.i64 value))
    (h4 : frame.locals[4]? = some (.i64 0)) (hn : 4 ≤ frame.locals.size)
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
  have set := wp_after_return cfg fuel rest t limits base frame callers suffix mi index global scratch value post h2 hn hm' hi hg' ct tn
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
  have get3 := wp_local_get cfg (fuel + 23) (32 * op + rest) (paid s op 1) limits (base.toArray.push (.i64 0)) frame callers
    (.call 432 :: .local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix) 3 (.i64 value) post h3
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) (by simpa only [op,paid,List.cons_append,List.nil_append] using callNext)
  have get4 := wp_local_get cfg (fuel + 24) (op + (32 * op + rest)) s limits base.toArray frame callers
    (.local_get 3 :: .call 432 :: .local_set 3 :: [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3] ++ suffix) 4 (.i64 0) post h4
    (hc.mono (by dsimp [op]; omega)) (by simpa only [op,paid,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using get3)
  simpa only [code,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (32 * op + rest)) = 34 * cfg.regularOpCost + rest by dsimp [op]; omega] using get4
end WNear.Proofs.StateDispatchLengthFinish
