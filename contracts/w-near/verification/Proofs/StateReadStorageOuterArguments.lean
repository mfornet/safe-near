import Binary.StateReadStorageOuter
import Proofs.StorePairCallerState
import NearVM.MeteredWordRules

/-! Original548 scalar arguments, with arbitrary caller stack and frames. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_storage_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch))
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      (((stack).push (.i32 1055020)).push (.i32 (scratch+8))) frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadStorageOuter.storageArguments++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have p3 := wp_i32_add cfg fuel (rest) (paid s op 3) limits ((stack).push (.i32 1055020)) frame callers code scratch 8 post (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) hnext
  have p2 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 2) limits (((stack).push (.i32 1055020)).push (.i32 scratch)) frame callers (.i32_binop .add::code) 8 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_local_get cfg (fuel+2) (op+(op+(rest))) (paid s op 1) limits ((stack).push (.i32 1055020)) frame callers (.i32_const 8::.i32_binop .add::code) 3 (.i32 scratch) post h3 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_i32_const cfg (fuel+3) (op+(op+(op+(rest)))) s limits (stack) frame callers (.local_get 3::.i32_const 8::.i32_binop .add::code) 1055020 post (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(rest))))=4*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.StateReadStorageOuter.storageArguments,List.cons_append,List.nil_append,cost] using p0

theorem wp_register_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch))
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      (((stack).push (.i32 (scratch+16))).push (.i64 0)) frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadStorageOuter.registerArguments++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have p3 := wp_i64_const cfg fuel (rest) (paid s op 3) limits ((stack).push (.i32 (scratch+16))) frame callers code 0 post (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) hnext
  have p2 := wp_i32_add cfg (fuel+1) (op+(rest)) (paid s op 2) limits (stack) frame callers (.i64_const 0::code) scratch 16 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+2) (op+(op+(rest))) (paid s op 1) limits ((stack).push (.i32 scratch)) frame callers (.i32_binop .add::.i64_const 0::code) 16 post (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) s limits (stack) frame callers (.i32_const 16::.i32_binop .add::.i64_const 0::code) 3 (.i32 scratch) post h3 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(rest))))=4*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.StateReadStorageOuter.registerArguments,List.cons_append,List.nil_append,cost] using p0

theorem wp_option_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (out : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (h0 : frame.locals[0]?=some (.i32 out))
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      ((((((stack).push (.i32 out)).push (.i32 (scratch+16))).push (.i32 1055256)).push (.i32 68)).push (.i32 1056324)) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadStorageOuter.optionArguments++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have p6 := wp_i32_const cfg fuel (rest) (paid s op 6) limits (((((stack).push (.i32 out)).push (.i32 (scratch+16))).push (.i32 1055256)).push (.i32 68)) frame callers code 1056324 post (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have p5 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 5) limits ((((stack).push (.i32 out)).push (.i32 (scratch+16))).push (.i32 1055256)) frame callers (.i32_const 1056324::code) 68 post (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_const cfg (fuel+2) (op+(op+(rest))) (paid s op 4) limits (((stack).push (.i32 out)).push (.i32 (scratch+16))) frame callers (.i32_const 68::.i32_const 1056324::code) 1055256 post (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_i32_add cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 3) limits ((stack).push (.i32 out)) frame callers (.i32_const 1055256::.i32_const 68::.i32_const 1056324::code) scratch 16 post (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_const cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 2) limits (((stack).push (.i32 out)).push (.i32 scratch)) frame callers (.i32_binop .add::.i32_const 1055256::.i32_const 68::.i32_const 1056324::code) 16 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 1) limits ((stack).push (.i32 out)) frame callers (.i32_const 16::.i32_binop .add::.i32_const 1055256::.i32_const 68::.i32_const 1056324::code) 3 (.i32 scratch) post h3 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) s limits (stack) frame callers (.local_get 3::.i32_const 16::.i32_binop .add::.i32_const 1055256::.i32_const 68::.i32_const 1056324::code) 0 (.i32 out) post h0 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(rest)))))))=7*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.StateReadStorageOuter.optionArguments,List.cons_append,List.nil_append,cost] using p0
end WNear.Proofs.StateReadStorageOuter
