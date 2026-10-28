import Proofs.AllocateVectorOuterScalar

/-! Actual f687 arguments to the flag-one f686 branch. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch count : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (h2 : frame.locals[2]?=some (.i32 count))
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (scratch+8))).push (.i32 count)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVectorOuter.arguments++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have k1 := wp_i32_const cfg fuel rest (paid s op 4) limits ((stack.push (.i32 (scratch+8))).push (.i32 count)) frame callers code
    1 post (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have get2 := wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (scratch+8))) frame callers
    (.i32_const 1::code) 2 (.i32 count) post h2 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) k1
  have add := wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.local_get 2::.i32_const 1::code) scratch 8 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) get2
  have k8 := wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 2::.i32_const 1::code) 8 post (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) add
  have get3 := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 2::.i32_const 1::code) 3 (.i32 scratch) post h3 (hc.mono (by dsimp [op];omega)) k8
  have ce : cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at get3
  simpa only [WNear.Binary.AllocateVectorOuter.arguments,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using get3
end WNear.Proofs.AllocateVectorOuter
