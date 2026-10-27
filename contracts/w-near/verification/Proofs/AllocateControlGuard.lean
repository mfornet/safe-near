import Binary.AllocateControl
import Proofs.AllocateControlWords
import NearVM.MeteredSelectionRules
import NearVM.MeteredLoopRules
import Proofs.ValueReturnBorrow

/-! Both actual backlink guards pass for a nonzero low-flags-zero end word. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

def endReadFrame (frame : CallFrame) (finish : UInt32) :=
  {frame with locals:=(frame.locals.set! 2 (.i32 finish)).set! 10 (.i32 finish)}
def endSelectedFrame (frame : CallFrame) (finish : UInt32) :=
  {frame with locals:=frame.locals.set! 2 (.i32 finish)}

/-- The real first guard reads the old end before any backlink is written. -/
theorem wp_read_end_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head finish : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[1]? = some (.i32 head)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : head.toNat+4 ≤ memory.byteSize) (hread : readI32 memory head.toNat = finish)
    (hmask : finish &&& 4294967292 = finish) (hn : finish ≠ 0)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits stack (endReadFrame frame finish) callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers
      ([.local_get 1,.load .i32 none {align:=2,offset:=0},.local_tee 2,.i32_const 4294967292,
        .i32_binop .and,.local_tee 10,.i32_eqz,.br_if 0]++code))) (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let f1 : CallFrame := {frame with locals:=frame.locals.set! 2 (.i32 finish)}
  let f2 : CallFrame := {f1 with locals:=f1.locals.set! 10 (.i32 finish)}
  have nonzero : (finish == 0) = false := by simp [hn]
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid,chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  rw [show 8*cfg.regularOpCost+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+7) _ s limits stack frame callers _ 1 (.i32 head) post hl (hc.mono (by dsimp [op]; omega))
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel+6) _ (paid s op 1) limits stack frame callers _ {align:=2,offset:=0} head mi index memory post hm1 hi hmem1 (by simpa using hr)
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero,hread]
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+5) _ (paid s op 2) limits stack frame callers _ 2 (.i32 finish) post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+4) _ (paid s op 3) limits _ f1 callers _ 4294967292 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+3) _ (paid s op 4) limits stack f1 callers _ finish 4294967292 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [hmask]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+2) _ (paid s op 5) limits stack f1 callers _ 10 (.i32 finish) post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+1) _ (paid s op 6) limits stack f2 callers _ finish post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  simp only [nonzero,Numeric.bool]
  apply wp_br_if_zero cfg fuel rest (paid s op 7) limits stack f2 callers code 0 post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [f2,f1,endReadFrame,op,paid] using hnext

theorem wp_select_end_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (finish : UInt32) (post : Post)
    (h2 : frame.locals[2]? = some (.i32 finish)) (h10 : frame.locals[10]? = some (.i32 finish))
    (hf : finish &&& 2 = 0) (hn : finish ≠ 0) (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits stack (endSelectedFrame frame finish) callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers
      ([.i32_const 0,.local_get 10,.local_get 2,.i32_const 2,.i32_binop .and,.select none,.local_tee 2,.i32_eqz,.br_if 0]++code)))
      (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let selected := endSelectedFrame frame finish
  have nonzero : (finish == 0) = false := by simp [hn]
  rw [show 9*cfg.regularOpCost+rest=cfg.regularOpCost+(8*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+8) _ s limits stack frame callers _ 0 post (hc.mono (by dsimp [op]; omega))
  rw [show 8*op+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+7) _ (paid s op 1) limits _ frame callers _ 10 (.i32 finish) post h10
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ (paid s op 2) limits _ frame callers _ 2 (.i32 finish) post h2
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+5) _ (paid s op 3) limits _ frame callers _ 2 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+4) _ (paid s op 4) limits ((stack.push (.i32 0)).push (.i32 finish)) frame callers _ finish 2 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [hf]
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_select cfg (fuel+3) _ (paid s op 5) limits stack frame callers _ (.i32 0) (.i32 finish) 0 post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  simp only [ne_eq,not_true_eq_false,ite_false]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+2) _ (paid s op 6) limits stack frame callers _ 2 (.i32 finish) post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+1) _ (paid s op 7) limits stack selected callers _ finish post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  simp only [nonzero,Numeric.bool]
  apply wp_br_if_zero cfg fuel rest (paid s op 8) limits stack selected callers code 0 post
  · exact paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [selected,endSelectedFrame,op,paid] using hnext

def backlinkFrame (frame : CallFrame) (finish : UInt32) := endSelectedFrame (endReadFrame frame finish) finish

/-- Both actual backlink guards, composed without any source-state mutation. -/
theorem wp_backlink_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head finish : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[1]? = some (.i32 head)) (hs : 11 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hr : head.toNat+4 ≤ memory.byteSize)
    (hread : readI32 memory head.toNat = finish) (hmask : finish &&& 4294967292 = finish)
    (hf : finish &&& 2 = 0) (hn : finish ≠ 0) (hc : s.host.gas.Credits (17*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 17) limits stack (backlinkFrame frame finish) callers code)) rest post) :
    WP cfg (fuel+17) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateSearch.backlinkGuard++code)))
      (17*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have h2 : 2 < frame.locals.size := by omega
  have h10 : 10 < frame.locals.size := by omega
  have two : (endReadFrame frame finish).locals[2]? = some (.i32 finish) := by simp [endReadFrame,h2]
  have ten : (endReadFrame frame finish).locals[10]? = some (.i32 finish) := by simp [endReadFrame,h10]
  have cs := paid_credits s op 8 (9*op+rest) (hc.mono (by dsimp [op]; omega))
  have selectNext : WP cfg fuel (.next (atCode (paid (paid s op 8) op 9) limits stack
      (endSelectedFrame (endReadFrame frame finish) finish) callers code)) rest post := by
    simpa only [ValueReturnBorrow.paid_add,Nat.reduceAdd,backlinkFrame,op] using hnext
  have select := wp_select_end_guard cfg fuel rest (paid s op 8) limits stack (endReadFrame frame finish) callers code finish post
    two ten hf hn cs selectNext
  have result := wp_read_end_guard cfg (fuel+9) (9*op+rest) s limits stack frame callers
    ([.i32_const 0,.local_get 10,.local_get 2,.i32_const 2,.i32_binop .and,.select none,.local_tee 2,.i32_eqz,.br_if 0]++code)
    head finish mi index memory post hl hm hi hmem hr hread hmask hn (hc.mono (by dsimp [op]; omega)) select
  have cost : 8*cfg.regularOpCost+(9*op+rest)=17*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [WNear.Binary.AllocateSearch.backlinkGuard,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocateSearch
