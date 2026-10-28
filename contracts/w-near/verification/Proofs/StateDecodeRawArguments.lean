import Proofs.StateDecodeRawGuards
import NearVM.MeteredScalarRules

/-! Real f769 argument construction, preserving arbitrary caller stack prefixes. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def arguments770Code : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.local_get 1,.local_get 2,.i32_const 0]

theorem wp_arguments770 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch size alignment : UInt32) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 size)) (h2 : frame.locals[2]?=some (.i32 alignment))
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((((stack.push (.i32 (scratch+8))).push (.i32 size)).push (.i32 alignment)).push (.i32 0)) frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (arguments770Code++code))) (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have zero:=wp_i32_const cfg fuel rest (paid s op 5) limits (((stack.push (.i32 (scratch+8))).push (.i32 size)).push (.i32 alignment)) frame callers code 0 post
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) hnext
  have align:=wp_local_get cfg (fuel+1) (op+rest) (paid s op 4) limits ((stack.push (.i32 (scratch+8))).push (.i32 size)) frame callers (.i32_const 0::code) 2 (.i32 alignment) post h2
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) zero
  have sz:=wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 (scratch+8))) frame callers (.local_get 2::.i32_const 0::code) 1 (.i32 size) post h1
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) align
  have add:=wp_i32_add cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack frame callers
    (.local_get 1::.local_get 2::.i32_const 0::code) scratch 8 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) sz
  have eight:=wp_i32_const cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 1::.local_get 2::.i32_const 0::code) 8 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get:=wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 1::.local_get 2::.i32_const 0::code) 3 (.i32 scratch) post h3
    (hc.mono (by dsimp[op];omega)) eight
  simpa only[arguments770Code,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeRaw
