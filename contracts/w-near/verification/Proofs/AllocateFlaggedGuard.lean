import Proofs.AllocateFlaggedState
import Proofs.AllocateControlGuard

/-! The flags-two backlink path selects zero and exits the actual block. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout endSelectedFrame)
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

def endReadFrame (frame : CallFrame) (raw finish : UInt32) :=
  {frame with locals:=(frame.locals.set! 2 (.i32 raw)).set! 10 (.i32 finish)}

theorem wp_read_end_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head raw finish : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[1]? = some (.i32 head)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : head.toNat+4 ≤ memory.byteSize) (hread : readI32 memory head.toNat = raw)
    (hmask : raw &&& 4294967292 = finish) (hn : finish ≠ 0)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits stack (endReadFrame frame raw finish) callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers
      ([.local_get 1,.load .i32 none {align:=2,offset:=0},.local_tee 2,.i32_const 4294967292,
        .i32_binop .and,.local_tee 10,.i32_eqz,.br_if 0]++code))) (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let f1 : CallFrame := {frame with locals:=frame.locals.set! 2 (.i32 raw)}
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
  apply wp_local_tee cfg (fuel+5) _ (paid s op 2) limits stack frame callers _ 2 (.i32 raw) post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+4) _ (paid s op 3) limits _ f1 callers _ 4294967292 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+3) _ (paid s op 4) limits stack f1 callers _ raw 4294967292 post
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

/-- A set low header flag selects zero, so br_if exits instead of writing an end backlink. -/
theorem wp_select_skip (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code discarded : Expr) (raw finish : UInt32) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 raw)) (h10 : frame.locals[10]?=some (.i32 finish))
    (hf : raw &&& 2=2) (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits stack (endSelectedFrame frame 0) callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      ([.i32_const 0,.local_get 10,.local_get 2,.i32_const 2,.i32_binop .and,.select none,.local_tee 2,.i32_eqz,.br_if 0]++discarded)))
      (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  let selected := endSelectedFrame frame 0
  rw [show 9*cfg.regularOpCost+rest=cfg.regularOpCost+(8*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+8) _ s limits stack bf callers _ 0 post (hc.mono (by dsimp [op]; omega))
  rw [show 8*op+rest=cfg.regularOpCost+(7*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+7) _ (paid s op 1) limits _ bf callers _ 10 (.i32 finish) post h10
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 7*op+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ (paid s op 2) limits _ bf callers _ 2 (.i32 raw) post h2
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+5) _ (paid s op 3) limits _ bf callers _ 2 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel+4) _ (paid s op 4) limits ((stack.push (.i32 0)).push (.i32 finish)) bf callers _ raw 2 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [hf]
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_select cfg (fuel+3) _ (paid s op 5) limits stack bf callers _ (.i32 0) (.i32 finish) 2 post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  simp only [ne_eq,show ((2:UInt32)=0)=False by decide,not_false_eq_true,ite_true]
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel+2) _ (paid s op 6) limits stack bf callers _ 2 (.i32 0) post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_eqz cfg (fuel+1) _ (paid s op 7) limits stack (emptyBlockFrame selected stack.size code) callers _ 0 post
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  have branchNext : WP cfg fuel (.next (atCode (chargedStore (paid s op 8) cfg.regularOpCost) limits stack selected callers code)) rest post := by
    simpa only [paid,op] using hnext
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 8) limits stack selected callers code discarded 1 post
    (by decide) (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) branchNext
  simpa only [bf,selected,endSelectedFrame,emptyBlockFrame,Numeric.bool,BEq.rfl,ite_true,paid,op,List.append_eq,List.cons_append,List.nil_append] using branch
def backlinkFrame (frame : CallFrame) (raw finish : UInt32) := endSelectedFrame (endReadFrame frame raw finish) 0

/-- The actual backlink block skips its write and has no fall-through label step. -/
theorem wp_backlink_skip (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (head raw finish : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[1]?=some (.i32 head)) (hs : 11≤frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hr : head.toNat+4≤memory.byteSize)
    (hread : readI32 memory head.toNat=raw) (hmask : raw &&& 4294967292=finish)
    (hflag : raw &&& 2=2) (hn : finish≠0) (hc : s.host.gas.Credits (17*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 17) limits stack (backlinkFrame frame raw finish) callers code)) rest post) :
    WP cfg (fuel+18) (.next (atCode s limits stack frame callers
      (.block .empty WNear.Binary.AllocateSearch.backlinkBody::code))) (17*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let first := endReadFrame frame raw finish
  have c8 := paid_credits s op 8 (9*op+rest) (hc.mono (by dsimp [op]; omega))
  have first2 : first.locals[2]?=some (.i32 raw) := by simp [first,endReadFrame,show 2<frame.locals.size by omega]
  have first10 : first.locals[10]?=some (.i32 finish) := by simp [first,endReadFrame,show 10<frame.locals.size by omega]
  have sn : WP cfg fuel (.next (atCode (paid (paid s op 8) cfg.regularOpCost 9) limits stack (endSelectedFrame first 0) callers code)) rest post := by
    simpa only [backlinkFrame,first,ValueReturnBorrow.paid_add,Nat.reduceAdd,op] using hnext
  have select := wp_select_skip cfg fuel rest (paid s op 8) limits stack first callers code WNear.Binary.AllocateSearch.backlinkWrite raw finish post first2 first10 hflag c8 sn
  have rn : WP cfg (fuel+9) (.next (atCode (paid s cfg.regularOpCost 8) limits stack
      (endReadFrame (emptyBlockFrame frame stack.size code) raw finish) callers
      ([.i32_const 0,.local_get 10,.local_get 2,.i32_const 2,.i32_binop .and,.select none,.local_tee 2,.i32_eqz,.br_if 0]++WNear.Binary.AllocateSearch.backlinkWrite)))
      (9*op+rest) post := by
    simpa only [first,endReadFrame,emptyBlockFrame] using select
  have read := wp_read_end_guard cfg (fuel+9) (9*op+rest) s limits stack (emptyBlockFrame frame stack.size code) callers
    ([.i32_const 0,.local_get 10,.local_get 2,.i32_const 2,.i32_binop .and,.select none,.local_tee 2,.i32_eqz,.br_if 0]++WNear.Binary.AllocateSearch.backlinkWrite)
    head raw finish mi index memory post hl hm hi hmem hr hread hmask hn (hc.mono (by dsimp [op]; omega)) rn
  have cost : 8*cfg.regularOpCost+(9*op+rest)=17*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at read
  apply wp_block_empty cfg (fuel+17) _ s limits stack frame callers WNear.Binary.AllocateSearch.backlinkBody code post hc
  simpa only [WNear.Binary.AllocateSearch.backlinkBody,WNear.Binary.AllocateSearch.backlinkGuard,List.append_assoc,
    List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using read
end WNear.Proofs.AllocateFlagged
