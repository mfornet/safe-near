import Proofs.AllocateVectorOuterArguments
import Proofs.InterfaceStack
import NearVM.MeteredSelectionRules

/-! Actual f687 branch over its fallback and restoration of the32-byte shadow frame. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

def exitAfter (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  setGlobal (paid s op 5) index (.i32 (scratch+32))
def outerFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame frame height (WNear.Binary.AllocateVectorOuter.restore++code)
def nestedFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame (outerFrame frame height code) height WNear.Binary.AllocateVectorOuter.alternative

theorem wp_exit (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (global : GlobalInst) (scratch : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.globalAddrs[0]?=some index)
    (hg : s.globals[index]?=some global)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (exitAfter s cfg.regularOpCost index scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack (nestedFrame frame stack.size code) callers [.br 1]))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have next : WP cfg fuel (.next (atCode (setGlobal (paid (chargedStore s op) op 4) index (.i32 (scratch+32)))
      limits stack frame callers code)) rest post := by simpa only [exitAfter,paid,op] using hnext
  have restore := InterfaceStack.wp_restore cfg fuel rest (chargedStore s op) limits stack frame callers code mi index global scratch 3 32 post
    h3 hm hi hg (StorePair.charged_credits s op _ (hc.mono (by dsimp [op];omega))) next
  have branchNext : WP cfg (fuel+4) (.next (atCode (chargedStore s cfg.regularOpCost) limits stack frame callers
      (WNear.Binary.AllocateVectorOuter.restore++code))) (4*op+rest) post := by
    simpa only [WNear.Binary.AllocateVectorOuter.restore,op] using restore
  have branch := wp_br_two_blocks cfg (fuel+4) (4*op+rest) s limits stack frame callers
    (WNear.Binary.AllocateVectorOuter.restore++code) WNear.Binary.AllocateVectorOuter.alternative [] post
    (hc.mono (by dsimp [op];omega)) branchNext
  have ce : cfg.regularOpCost+(4*op+rest)=5*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at branch
  simpa only [nestedFrame,outerFrame,Nat.add_assoc,Nat.reduceAdd] using branch
end WNear.Proofs.AllocateVectorOuter
