import Binary.StateDecodeRaw
import Proofs.AllocateVectorGuard

/-! The f767 layout guards share the exact deployed checks of f686. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateVector (loadedFrame)
attribute [local irreducible] WP atCode readI32

theorem wp_alignment_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+28+4≤memory.byteSize) (ha : readI32 memory (scratch.toNat+28)=1)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack
      (loadedFrame frame 1 1) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeRaw.alignmentGuard++code)))
      (5*cfg.regularOpCost+rest) post := by
  exact AllocateVector.wp_alignment_guard cfg fuel rest s limits stack frame callers code scratch mi index memory post h3 hm hi hmem hb ha hc hnext

theorem wp_size_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch size : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+24+4≤memory.byteSize) (ha : readI32 memory (scratch.toNat+24)=size)
    (hn : size.toNat<2^31)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack
      (loadedFrame frame 4 size) callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeRaw.sizeGuard++code))) (6*cfg.regularOpCost+rest) post := by
  exact AllocateVector.wp_size_guard cfg fuel rest s limits stack frame callers code scratch size mi index memory post h3 hm hi hmem hb ha hn hc hnext
end WNear.Proofs.StateDecodeRaw
