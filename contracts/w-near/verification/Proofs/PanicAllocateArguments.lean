import Proofs.PanicAllocateCopy

/-! Actual scalar argument setup in the panic allocation wrappers. -/
namespace WNear.Proofs.PanicAllocateArguments
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
attribute [local irreducible] WP

theorem wp_arguments5 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (outSlot sizeSlot alignmentSlot : Nat) (scratch size alignment : UInt32) (post : Post)
    (hs : frame.locals[outSlot]? = some (.i32 scratch)) (hz : frame.locals[sizeSlot]? = some (.i32 size))
    (ha : frame.locals[alignmentSlot]? = some (.i32 alignment))
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (scratch + 8))).push (.i32 size)).push (.i32 alignment)) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get outSlot, .i32_const 8, .i32_binop .add, .local_get sizeSlot, .local_get alignmentSlot] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have a := wp_local_get cfg fuel rest (paid s op 4) limits
    ((stack.push (.i32 (scratch + 8))).push (.i32 size)) frame callers code alignmentSlot (.i32 alignment) post ha
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) hnext
  have z := wp_local_get cfg (fuel + 1) (op + rest) (paid s op 3) limits
    (stack.push (.i32 (scratch + 8))) frame callers (.local_get alignmentSlot :: code) sizeSlot (.i32 size) post hz
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) a
  have add := wp_i32_add cfg (fuel + 2) (op + (op + rest)) (paid s op 2) limits stack frame callers
    (.local_get sizeSlot :: .local_get alignmentSlot :: code) scratch 8 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) z
  have c := wp_i32_const cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 1) limits
    (stack.push (.i32 scratch)) frame callers (.i32_binop .add :: .local_get sizeSlot :: .local_get alignmentSlot :: code) 8 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) add
  have result := wp_local_get cfg (fuel + 4) (op + (op + (op + (op + rest)))) s limits stack frame callers
    (.i32_const 8 :: .i32_binop .add :: .local_get sizeSlot :: .local_get alignmentSlot :: code) outSlot (.i32 scratch) post hs
    (hc.mono (by dsimp [op]; omega)) c
  have ge : cfg.regularOpCost + (op + (op + (op + (op + rest)))) = 5 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post rfl ge rfl result

theorem wp_arguments508 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch size alignment : UInt32) (post : Post)
    (hs : frame.locals[3]? = some (.i32 scratch)) (hz : frame.locals[1]? = some (.i32 size))
    (ha : frame.locals[2]? = some (.i32 alignment))
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((((stack.push (.i32 (scratch + 8))).push (.i32 size)).push (.i32 alignment)).push (.i32 0)) frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers (WNear.Binary.PanicAllocate.arguments508 ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  have cp := paid_credits s cfg.regularOpCost 5 (cfg.regularOpCost + rest) (hc.mono (by omega))
  have constant := wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 5) limits
    (((stack.push (.i32 (scratch + 8))).push (.i32 size)).push (.i32 alignment)) frame callers code 0 post cp hnext
  have result := wp_arguments5 cfg (fuel + 1) (cfg.regularOpCost + rest) s limits stack frame callers
    (.i32_const 0 :: code) 3 1 2 scratch size alignment post hs hz ha (hc.mono (by omega)) constant
  have fe : fuel + 1 + 5 = fuel + 6 := by omega
  have ge : 5 * cfg.regularOpCost + (cfg.regularOpCost + rest) = 6 * cfg.regularOpCost + rest := by omega
  have ce : [.local_get 3, .i32_const 8, .i32_binop .add, .local_get 1, .local_get 2] ++ (.i32_const 0 :: code) =
      WNear.Binary.PanicAllocate.arguments508 ++ code := rfl
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post fe ge ce result

end WNear.Proofs.PanicAllocateArguments
