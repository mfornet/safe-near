import Proofs.StateDecodePrefixEarlyPhases
import Proofs.InterfaceStack

/-! Actual316 reserves sixty-four shadow-stack bytes and keeps the scratch
address in local2. Its arithmetic remains the actual UInt32 arithmetic. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode

theorem wp_prefix_setup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (p : Layout) (post : Post) (hcode : Code s frame.inst p)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (reservedPrefix s cfg.regularOpCost p) limits stack
      (reservedPrefixFrame frame p) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefix.setup++code)))
      (5*cfg.regularOpCost+rest) post := by
  have result:=InterfaceStack.wp_reserve cfg fuel rest s limits stack frame callers code p.mi p.globalIndex p.global p.sp 2 64 post
    hcode.module hcode.globalIndex hg hv hc hnext
  simpa only[WNear.Binary.StateDecodePrefix.setup] using result
end WNear.Proofs.StateDecodePrefix
