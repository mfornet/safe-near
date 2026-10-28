import Proofs.StateDecodeScalarOutput

/-! Update the caller slice from its cached descriptor, then mark the local success tag. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode store64Local

def zeroFrame (frame : CallFrame) := {frame with locals:=frame.locals.set! 1 (.i32 0)}
def updateStore (s : Store NearState) (op index : Nat) (memory : Memory) (slice : UInt32) (packed : UInt64) :=
  paid (store64Local s op index memory slice packed) op 2

theorem wp_update_slice (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (wide : Bool) (slice : UInt32) (packed : UInt64) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (hp : frame.locals[if wide then 6 else 5]?=some (.i64 packed))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : slice.toNat+8≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (updateStore s cfg.regularOpCost index memory slice packed)
      limits stack (zeroFrame frame) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeScalar.updateSlice wide++code))) (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let updated:=store64Local s op index memory slice packed
  have cu : updated.host.gas.Credits (2*op+rest) := by
    unfold updated store64Local
    rw [storeI64_host]
    exact paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))
  have set := wp_local_set cfg fuel rest (paid updated op 1) limits stack frame callers code 1 (.i32 0) post
    (paid_credits updated op 1 _ (cu.mono (by omega)))
    (by simpa only [zeroFrame,updateStore,updated,paid,op] using hnext)
  have constant := wp_i32_const cfg (fuel+1) (op+rest) updated limits stack frame callers (.local_set 1::code) 0 post
    (cu.mono (by omega)) set
  have stored := wp_store64_local cfg (fuel+2) (2*op+rest) s limits stack frame callers
    (.i32_const 0::.local_set 1::code) 1 (if wide then 6 else 5) slice packed mi index memory post h1 hp hm hi hmem hb
    (hc.mono (by dsimp[op];omega))
    (by simpa only [updated,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(op+rest)=2*op+rest by dsimp[op];omega] using constant)
  simpa only [WNear.Binary.StateDecodeScalar.updateSlice,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(2*op+rest)=5*cfg.regularOpCost+rest by dsimp[op];omega] using stored
end WNear.Proofs.StateDecodeScalar
