import Proofs.AllocateVectorPhases

/-! Actual scalar arguments to685 and690; pointer addition remains UInt32 arithmetic. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_layout_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch size : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (h1 : frame.locals[1]?=some (.i32 size))
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 (scratch+24))).push (.i32 size)) frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVector.layoutArguments++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have g1 := wp_local_get cfg fuel rest (paid s op 3) limits (stack.push (.i32 (scratch+24))) frame callers code
    1 (.i32 size) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) hnext
  have add := wp_i32_add cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers
    (.local_get 1::code) scratch 24 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) g1
  have k := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 1::code) 24 post (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) add
  have g := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.i32_const 24::.i32_binop .add::.local_get 1::code) 3 (.i32 scratch) post h3 (hc.mono (by dsimp [op];omega)) k
  simpa only [WNear.Binary.AllocateVector.layoutArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp [op];omega] using g

theorem wp_allocate_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch size : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (h4 : frame.locals[4]?=some (.i32 size))
    (h1 : frame.locals[1]?=some (.i32 1))
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (scratch+8))).push (.i32 size)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVector.allocateArguments++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have g1 := wp_local_get cfg fuel rest (paid s op 4) limits ((stack.push (.i32 (scratch+8))).push (.i32 size)) frame callers code
    1 (.i32 1) post h1 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have g4 := wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (scratch+8))) frame callers
    (.local_get 1::code) 4 (.i32 size) post h4 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) g1
  have add := wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.local_get 4::.local_get 1::code) scratch 8 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) g4
  have k := wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 4::.local_get 1::code) 8 post (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) add
  have g := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 4::.local_get 1::code) 3 (.i32 scratch) post h3 (hc.mono (by dsimp [op];omega)) k
  simpa only [WNear.Binary.AllocateVector.allocateArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp [op];omega] using g
end WNear.Proofs.AllocateVector
