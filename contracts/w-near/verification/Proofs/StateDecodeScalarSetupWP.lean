import Proofs.StateDecodeScalarState
import Proofs.InterfaceStack

/-! Actual scalar-wrapper shadow-stack reservation. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode

theorem wp_setup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (reserved s cfg.regularOpCost p) limits stack (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeScalar.setup++code)))
      (5*cfg.regularOpCost+rest) post := by
  have h := InterfaceStack.wp_reserve cfg fuel rest s limits stack frame callers code p.mi p.globalIndex p.global p.sp 2 48 post hm hi hg hv hc hnext
  simpa only [WNear.Binary.StateDecodeScalar.setup] using h
end WNear.Proofs.StateDecodeScalar
