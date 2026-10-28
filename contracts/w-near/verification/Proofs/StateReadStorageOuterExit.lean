import Binary.StateReadStorageOuter
import Proofs.InterfaceStack
import NearVM.MeteredLoopRules

/-! The selected548 path exits its remaining block and restores the shadow stack. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

theorem wp_exit (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (global : GlobalInst) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.globalAddrs[0]?=some index)
    (hg : s.globals[index]?=some global) (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch+32)))
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack
      (emptyBlockFrame frame stack.size (WNear.Binary.StateReadStorageOuter.restore++code)) callers []))
      (4*cfg.regularOpCost+rest) post := by
  have restore := InterfaceStack.wp_restore cfg fuel rest s limits stack frame callers code mi index global scratch 3 32 post h3 hm hi hg hc hnext
  have after : WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateReadStorageOuter.restore++code))) (4*cfg.regularOpCost+rest) post := by
    simpa only [WNear.Binary.StateReadStorageOuter.restore] using restore
  have ending := wp_end_label cfg (fuel+4) (4*cfg.regularOpCost+rest) s limits stack frame callers
    {arity:=0,height:=stack.size,rest:=WNear.Binary.StateReadStorageOuter.restore++code,loop:=none} post hc after
  simpa only [emptyBlockFrame,Nat.add_assoc,Nat.reduceAdd] using ending
end WNear.Proofs.StateReadStorageOuter
