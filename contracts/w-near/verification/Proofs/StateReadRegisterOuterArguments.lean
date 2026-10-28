import Proofs.StateReadRegisterOuterSteps

/-! Actual523 vector-allocation and register-read arguments. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode readI64

theorem wp_vector_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+16+8≤memory.byteSize)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 (scratch+32))).push (.i32 0)).push (.i32 (readI64 memory (scratch.toNat+16)).toUInt32)) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.vectorArguments++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let value := readI64 memory (scratch.toNat+16)
  have cv := wp_i32_wrap_i64 cfg fuel rest (paid s op 6) limits ((stack.push (.i32 (scratch+32))).push (.i32 0)) frame callers code value post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have mm5 : (paid s op 5).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have me5 : (paid s op 5).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have cvn : WP cfg (fuel+1) (.next (atCode (chargedStore (paid s op 5) op) limits
      (((stack.push (.i32 (scratch+32))).push (.i32 0)).push (.i64 (readI64 memory (scratch.toNat+16)))) frame callers (.cvt .i32_wrap_i64::code))) (op+rest) post := by
    simpa only [value,paid,op] using cv
  have ld := wp_i64_load cfg (fuel+1) (op+rest) (paid s op 5) limits ((stack.push (.i32 (scratch+32))).push (.i32 0)) frame callers
    (.cvt .i32_wrap_i64::code) {align:=3,offset:=16} scratch mi index memory post mm5 hi me5 hb
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) cvn
  have g2 := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 4) limits ((stack.push (.i32 (scratch+32))).push (.i32 0)) frame callers
    (.load .i64 none {align:=3,offset:=16}::.cvt .i32_wrap_i64::code) 2 (.i32 scratch) post h2
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) ld
  have k0 := wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 3) limits (stack.push (.i32 (scratch+32))) frame callers
    (.local_get 2::.load .i64 none {align:=3,offset:=16}::.cvt .i32_wrap_i64::code) 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) g2
  have add := wp_i32_add cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 2) limits stack frame callers
    (.i32_const 0::.local_get 2::.load .i64 none {align:=3,offset:=16}::.cvt .i32_wrap_i64::code) scratch 32 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) k0
  have k32 := wp_i32_const cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.i32_const 0::.local_get 2::.load .i64 none {align:=3,offset:=16}::.cvt .i32_wrap_i64::code) 32 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) add
  have g := wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) s limits stack frame callers
    (.i32_const 32::.i32_binop .add::.i32_const 0::.local_get 2::.load .i64 none {align:=3,offset:=16}::.cvt .i32_wrap_i64::code) 2 (.i32 scratch) post h2
    (hc.mono (by dsimp [op];omega)) k32
  simpa only [WNear.Binary.StateReadRegisterOuter.vectorArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+rest))))))=7*cfg.regularOpCost+rest by dsimp [op];omega] using g

theorem wp_read_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 1055020)).push (.i32 (scratch+24))).push (.i32 (scratch+32))) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.readArguments++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have add32 := wp_i32_add cfg fuel rest (paid s op 6) limits ((stack.push (.i32 1055020)).push (.i32 (scratch+24))) frame callers code scratch 32 post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have k32 := wp_i32_const cfg (fuel+1) (op+rest) (paid s op 5) limits (((stack.push (.i32 1055020)).push (.i32 (scratch+24))).push (.i32 scratch)) frame callers
    (.i32_binop .add::code) 32 post (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) add32
  have g2b := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 4) limits ((stack.push (.i32 1055020)).push (.i32 (scratch+24))) frame callers
    (.i32_const 32::.i32_binop .add::code) 2 (.i32 scratch) post h2 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) k32
  have add24 := wp_i32_add cfg (fuel+3) (op+(op+(op+rest))) (paid s op 3) limits (stack.push (.i32 1055020)) frame callers
    (.local_get 2::.i32_const 32::.i32_binop .add::code) scratch 24 post (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) g2b
  have k24 := wp_i32_const cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 2) limits ((stack.push (.i32 1055020)).push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 2::.i32_const 32::.i32_binop .add::code) 24 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) add24
  have g2 := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 1) limits (stack.push (.i32 1055020)) frame callers
    (.i32_const 24::.i32_binop .add::.local_get 2::.i32_const 32::.i32_binop .add::code) 2 (.i32 scratch) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) k24
  have con := wp_i32_const cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) s limits stack frame callers
    (.local_get 2::.i32_const 24::.i32_binop .add::.local_get 2::.i32_const 32::.i32_binop .add::code) 1055020 post
    (hc.mono (by dsimp [op];omega)) g2
  simpa only [WNear.Binary.StateReadRegisterOuter.readArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+rest))))))=7*cfg.regularOpCost+rest by dsimp [op];omega] using con
end WNear.Proofs.StateReadRegisterOuter
