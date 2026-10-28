import Proofs.StateDecodeScalarCache

/-! Cache the post-split slice descriptor before caller output writes. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

def dropCacheFrame (wide : Bool) (frame : CallFrame) (memory : Memory) (scratch : UInt32) :=
  loaded64Frame frame (if wide then 6 else 5) (readI64 memory (scratch.toNat+(if wide then 0 else 8)))

theorem wp_drop_cache (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+16≤memory.byteSize) (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      (dropCacheFrame wide frame memory scratch) callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeScalar.dropCache wide++code))) (3*cfg.regularOpCost+rest) post := by
  have bound : scratch.toNat+(if wide then 0 else 8)+8≤memory.byteSize := by
    cases wide with
    | false=>simpa using hb
    | true=>simp only [ite_true,Nat.add_zero];omega
  have step := wp_load64_local cfg fuel rest s limits stack frame callers code 2 (if wide then 6 else 5)
    {align:=3,offset:=if wide then 0 else 8} scratch mi index memory post h2 hm hi hmem bound hc hnext
  simpa only [WNear.Binary.StateDecodeScalar.dropCache,List.cons_append,List.nil_append] using step
end WNear.Proofs.StateDecodeScalar
