import Binary.StateReadRegisterOuter
import Proofs.StorePairCallerState
import NearVM.MeteredWordRules
import NearVM.MeteredNumericRules

/-! Actual523 register save and scalar arguments, independent of callee execution. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64 writeI64

def saved (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) (register : UInt64) :=
  storeI64 (paid s op 3) index (scratch.toNat+24) memory register

theorem wp_save_register (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (register : UInt64) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (h1 : frame.locals[1]?=some (.i64 register))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+24+8≤memory.byteSize)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (saved s cfg.regularOpCost index memory scratch register) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.saveRegister++code)))
      (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have st := wp_i64_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=3,offset:=24}
    scratch register mi index memory post hm hi hmem hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hnext
  have get1 := wp_local_get cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.store .i64 none {align:=3,offset:=24}::code) 1 (.i64 register) post h1
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) st
  have get2 := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.local_get 1::.store .i64 none {align:=3,offset:=24}::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) get1
  simpa only [WNear.Binary.StateReadRegisterOuter.saveRegister,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp [op];omega] using get2

theorem wp_length_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (register : UInt64) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (h1 : frame.locals[1]?=some (.i64 register))
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 (scratch+8))).push (.i64 register)) frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.lengthArguments++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have g1 := wp_local_get cfg fuel rest (paid s op 3) limits (stack.push (.i32 (scratch+8))) frame callers code
    1 (.i64 register) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) hnext
  have add := wp_i32_add cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers
    (.local_get 1::code) scratch 8 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) g1
  have k := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 1::code) 8 post (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) add
  have g := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 1::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) k
  simpa only [WNear.Binary.StateReadRegisterOuter.lengthArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp [op];omega] using g
end WNear.Proofs.StateReadRegisterOuter
