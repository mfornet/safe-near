import Binary.AllocateGrowth
import NearVM.MeteredControlRules

/-! The four actual outer error blocks of f577, all exited by its accepted return. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode

def errorBlocks : Expr := [.block .empty ([.block .empty ([.block .empty ([.block .empty WNear.Binary.AllocateGrowth.accepted]++WNear.Binary.AllocateGrowth.panicAdd)]++WNear.Binary.AllocateGrowth.panicBits)]++WNear.Binary.AllocateGrowth.panicAdd)]++WNear.Binary.AllocateGrowth.panicFinal

def errorFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame height (WNear.Binary.AllocateGrowth.panicFinal++code))
    height WNear.Binary.AllocateGrowth.panicAdd) height WNear.Binary.AllocateGrowth.panicBits) height WNear.Binary.AllocateGrowth.panicAdd

theorem wp_error_blocks (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (post : Post) (hc : s.host.gas.Credits rest)
    (hnext : WP cfg fuel (.next (atCode s limits stack (errorFrame frame stack.size code) callers WNear.Binary.AllocateGrowth.accepted)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (errorBlocks++code))) rest post := by
  unfold errorBlocks
  simp only [List.cons_append,List.nil_append]
  apply wp_block_empty cfg (fuel+3) rest s limits stack frame callers _ _ post hc
  apply wp_block_empty cfg (fuel+2) rest s limits stack _ callers _ _ post hc
  apply wp_block_empty cfg (fuel+1) rest s limits stack _ callers _ _ post hc
  apply wp_block_empty cfg fuel rest s limits stack _ callers _ _ post hc
  simpa only [errorFrame] using hnext
end WNear.Proofs.AllocateGrowth
