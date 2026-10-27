import Binary.Deallocate
import Proofs.VectorDropPrefix

/-! The actual fixed allocator-address argument prefix of f237. -/
namespace WNear.Proofs.VectorDropPositive237
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP

/-- The deployed forwarder passes allocator1074896, pointer, length and
alignment to f582, retaining all lower operands and caller state. -/
theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer length alignment : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 pointer)) (hb : frame.locals[1]? = some (.i32 length)) (hv : frame.locals[2]? = some (.i32 alignment))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((((stack.push (.i32 1074896)).push (.i32 pointer)).push (.i32 length)).push (.i32 alignment)) frame callers (.call 582 :: code))) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers (WNear.Binary.Deallocate.entryBody ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have three := WNear.Proofs.VectorDrop.wp_three_arguments cfg fuel rest (paid s op 1) limits (stack.push (.i32 1074896)) frame callers
    (.call 582 :: code) pointer length alignment post ha hb hv (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) hnext
  have constant := wp_i32_const cfg (fuel + 3) (3 * op + rest) s limits stack frame callers
    (.local_get 0 :: .local_get 1 :: .local_get 2 :: .call 582 :: code) 1074896 post (hc.mono (by dsimp [op]; omega)) three
  simpa only [WNear.Binary.Deallocate.entryBody, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (3 * op + rest) = 4 * cfg.regularOpCost + rest by dsimp [op]; omega] using constant
end WNear.Proofs.VectorDropPositive237
