import Binary.StateDispatch
import Proofs.InterfaceStack
import NearVM.MeteredWordRules
import NearVM.MeteredControlRules

/-! Accepted actual f432 returns the second i64 after checking the status. -/
namespace WNear.Proofs.StateDispatchReturn
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def reserved (s : Store NearState) (op index : Nat) (sp : UInt32) :=
  setGlobal (paid s op 5) index (.i32 (sp - 16))
def reservedFrame (frame : CallFrame) (sp : UInt32) :=
  {frame with locals := frame.locals.set! 2 (.i32 (sp - 16))}
def suffixAfter (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  paid (setGlobal (paid s op 4) index (.i32 (scratch + 16))) op 1
def after (s : Store NearState) (op index : Nat) (sp : UInt32) :=
  suffixAfter (paid (reserved s op index sp) op 4) op index (sp - 16)

/-- The actual status check discards the panic path when its low word is zero. -/
theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (status : UInt64) (post : Post)
    (hs : frame.locals[0]? = some (.i64 status)) (hz : status.toUInt32 = 0)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      (.block .empty (WNear.Binary.StateDispatch.returnGuard ++ WNear.Binary.StateDispatch.returnPanic) :: code)))
      (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 3) limits stack frame callers code
    WNear.Binary.StateDispatch.returnPanic 1 post (by decide) (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have en : WP cfg (fuel + 1) (.next (atCode (paid s op 3) limits
      (stack.push (.i32 (Numeric.bool (status.toUInt32 == 0)))) bf callers (.br_if 0 :: WNear.Binary.StateDispatch.returnPanic))) (op + rest) post := by
    simpa only [hz,BEq.rfl,Numeric.bool,ite_true,bf,op] using branch
  have eqz := wp_i32_eqz cfg (fuel + 1) (op + rest) (paid s op 2) limits stack bf callers
    (.br_if 0 :: WNear.Binary.StateDispatch.returnPanic) status.toUInt32 post (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) en
  have wrap := wp_i32_wrap_i64 cfg (fuel + 2) (op + (op + rest)) (paid s op 1) limits stack bf callers
    (.i32_eqz :: .br_if 0 :: WNear.Binary.StateDispatch.returnPanic) status post (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) eqz
  have get := wp_local_get cfg (fuel + 3) (op + (op + (op + rest))) s limits stack bf callers
    (.cvt .i32_wrap_i64 :: .i32_eqz :: .br_if 0 :: WNear.Binary.StateDispatch.returnPanic) 0 (.i64 status) post hs
    (hc.mono (by dsimp [op]; omega)) wrap
  have inside : WP cfg (fuel + 4) (.next (atCode s limits stack bf callers
      (WNear.Binary.StateDispatch.returnGuard ++ WNear.Binary.StateDispatch.returnPanic))) (4 * op + rest) post := by
    simpa only [WNear.Binary.StateDispatch.returnGuard,List.cons_append,List.nil_append,
      show cfg.regularOpCost + (op + (op + (op + rest))) = 4 * op + rest by dsimp [op]; omega] using get
  have block := wp_block_empty cfg (fuel + 4) (4 * op + rest) s limits stack frame callers
    (WNear.Binary.StateDispatch.returnGuard ++ WNear.Binary.StateDispatch.returnPanic) code post hc inside
  simpa only [Nat.add_assoc,Nat.reduceAdd,op] using block

/-- Five actual suffix instructions restore SP and leave the return value. -/
theorem wp_suffix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (global : GlobalInst)
    (scratch : UInt32) (value : UInt64) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hv : frame.locals[1]? = some (.i64 value))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (suffixAfter s cfg.regularOpCost index scratch) limits
      (stack.push (.i64 value)) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDispatch.returnSuffix ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have c4 : (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 16))).host.gas.Credits
      (cfg.regularOpCost + rest) := paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  have last := wp_local_get cfg fuel rest (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 16))) limits stack frame callers code
    1 (.i64 value) post hv c4 hnext
  have first := InterfaceStack.wp_restore cfg (fuel + 1) (cfg.regularOpCost + rest) s limits stack frame callers (.local_get 1 :: code)
    mi index global scratch 2 16 post hs hm hi hg (hc.mono (by omega)) last
  simpa only [WNear.Binary.StateDispatch.returnSuffix,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4 * cfg.regularOpCost + (cfg.regularOpCost + rest) = 5 * cfg.regularOpCost + rest by omega] using first
/-- Complete fifteen-step accepted body of actual f432. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (global : GlobalInst)
    (sp : UInt32) (status value : UInt64) (post : Post)
    (hs : frame.locals[0]? = some (.i64 status)) (hv : frame.locals[1]? = some (.i64 value)) (hn : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp) (hz : status.toUInt32 = 0)
    (hc : s.host.gas.Credits (14 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index sp) limits
      (stack.push (.i64 value)) (reservedFrame frame sp) callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits stack frame callers (WNear.Binary.StateDispatch.returnBody ++ code)))
      (14 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let sf := reservedFrame frame sp
  let sr := reserved s op index sp
  let guarded := paid sr op 4
  have cr : sr.host.gas.Credits (9 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have cg : guarded.host.gas.Credits (5 * op + rest) := paid_credits sr op 4 _ (cr.mono (by omega))
  have fs : sf.locals[0]? = some (.i64 status) := by simpa [sf,reservedFrame] using hs
  have fv : sf.locals[1]? = some (.i64 value) := by simpa [sf,reservedFrame] using hv
  have fp : sf.locals[2]? = some (.i32 (sp - 16)) := by simp [sf,reservedFrame,show 2 < frame.locals.size by omega]
  have hm' : guarded.modules[sf.inst]? = some mi := by simpa only [guarded,sr,reserved,sf,reservedFrame,setGlobal,paid,chargedStore] using hm
  have gr : sr.globals[index]? = some {global with value := .i32 (sp - 16)} := by
    simp only [sr,reserved,setGlobal,paid,chargedStore]
    simp [Array.getElem?_modify,hg]
  have gg : guarded.globals[index]? = some {global with value := .i32 (sp - 16)} := by
    simpa only [guarded,paid,chargedStore] using gr
  have suffix := wp_suffix cfg fuel rest guarded limits stack sf callers code mi index {global with value := .i32 (sp - 16)} (sp - 16) value post
    fp fv hm' hi gg cg hnext
  have guard := wp_guard cfg (fuel + 5) (5 * op + rest) sr limits stack sf callers (WNear.Binary.StateDispatch.returnSuffix ++ code) status post fs hz
    (cr.mono (by omega)) suffix
  have gn : WP cfg (fuel + 10) (.next (atCode sr limits stack sf callers
      (.block .empty (WNear.Binary.StateDispatch.returnGuard ++ WNear.Binary.StateDispatch.returnPanic) :: WNear.Binary.StateDispatch.returnSuffix ++ code)))
      (9 * op + rest) post := by
    simpa only [List.cons_append,Nat.add_assoc,Nat.reduceAdd,
      show 4 * cfg.regularOpCost + (5 * op + rest) = 9 * op + rest by dsimp [op]; omega] using guard
  have headProof := InterfaceStack.wp_reserve cfg (fuel + 10) (9 * op + rest) s limits stack frame callers
    (.block .empty (WNear.Binary.StateDispatch.returnGuard ++ WNear.Binary.StateDispatch.returnPanic) :: WNear.Binary.StateDispatch.returnSuffix ++ code)
    mi index global sp 2 16 post hm hi hg hsp (hc.mono (by dsimp [op]; omega)) gn
  simpa only [WNear.Binary.StateDispatch.returnBody,WNear.Binary.StateDispatch.returnPrefix,List.append_eq,List.cons_append,List.nil_append,List.append_assoc,
    Nat.add_assoc,Nat.reduceAdd,show 5 * cfg.regularOpCost + (9 * op + rest) = 14 * cfg.regularOpCost + rest by dsimp [op]; omega] using headProof

end WNear.Proofs.StateDispatchReturn
