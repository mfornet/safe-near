import Proofs.ValueReturnOuter
import Proofs.InterfaceStack

/-! Actual f435 zero-status check and sixteen-byte guest stack restoration. -/
namespace WNear.Proofs.StateDispatchReadFinish
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def code : Expr := [.local_get 0,.call 433,.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]
def checked (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  ValueReturnOuter.checkAfter (paid s op 1) op index scratch
def after (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  setGlobal (paid (checked s op index scratch) op 4) index (.i32 (scratch+16))

private theorem checked_modules (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    (checked s op index scratch).modules = s.modules := by
  simp only [checked,ValueReturnOuter.checkAfter,ValueReturnOuter.nonnullEntry,ValueReturnBorrow.checkedStore,paid,chargedStore,setGlobal]
private theorem checked_globals (s : Store NearState) (op index : Nat) (scratch : UInt32)
    (global : GlobalInst) (hg : s.globals[index]? = some global) (hs : global.value = .i32 scratch) :
    (checked s op index scratch).globals = s.globals :=
  ValueReturnBorrow.checkedStore_globals (ValueReturnOuter.nonnullEntry (paid s op 1) op) op index scratch global hg hs

theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (suffix : List Instr) (mi : ModuleInst) (index address : Nat) (global : GlobalInst)
    (scratch : UInt32) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 0)) (h3 : frame.locals[3]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 scratch)
    (hfi : mi.funcAddrs[433]? = some address)
    (hfn : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.checkFunction))
    (hd : callers.length+1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index scratch) limits base.toArray frame callers suffix)) rest post) :
    WP cfg (fuel+20) (.next (atCode s limits base.toArray frame callers (code++suffix)))
      (27 * cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let t := checked s op index scratch
  have c1 : (paid s op 1).host.gas.Credits (22*op+(4*op+rest)) := paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  have ct : t.host.gas.Credits (4*op+rest) := ValueReturnOuter.checkAfter_credits (paid s op 1) op index _ scratch c1
  have mt : t.modules[frame.inst]? = some mi := by rw [checked_modules]; exact hm
  have gt : t.globals[index]? = some global := by rw [checked_globals s op index scratch global hg hsp]; exact hg
  have restore := InterfaceStack.wp_restore cfg fuel rest t limits base.toArray frame callers suffix mi index global scratch 3 16 post
    h3 mt hi gt ct hnext
  have cn : WP cfg (fuel+4) (.next (atCode t limits base.toArray frame callers
      ([.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]++suffix))) (4*op+rest) post := restore
  have call := ValueReturnOuter.wp_call_check cfg (fuel+4) (4*op+rest) (paid s op 1) limits base frame callers
    ([.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]++suffix) address frame.inst index mi mi global scratch post
    hm hfi hfn hm hi hg hsp hd c1 (by simpa only [t,checked,op] using cn)
  have stackEq : (base++[Value.i32 0]).toArray = base.toArray.push (.i32 0) := by apply Array.toList_inj.mp; simp
  have nextGet : WP cfg (fuel+19) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 0)) frame callers
      (.call 433::[.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]++suffix))) (26*op+rest) post := by
    simpa only [stackEq,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,
      show 22*cfg.regularOpCost+(4*op+rest)=26*op+rest by dsimp [op]; omega] using call
  have result := wp_local_get cfg (fuel+19) (26*op+rest) s limits base.toArray frame callers
    (.call 433::[.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]++suffix) 0 (.i32 0) post h0
    (hc.mono (by dsimp [op]; omega)) (by simpa only [paid,op] using nextGet)
  simpa only [code,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(26*op+rest)=27*cfg.regularOpCost+rest by dsimp [op]; omega] using result

end WNear.Proofs.StateDispatchReadFinish
