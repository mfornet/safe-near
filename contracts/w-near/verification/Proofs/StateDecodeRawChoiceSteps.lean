import Proofs.StateDecodeRawGuards
import NearVM.MeteredScalarRules

/-! The selected f767 flag-zero branch and actual f769 argument instructions. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

theorem wp_raw_flag_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code discarded : Expr) (post : Post) (h2 : frame.locals[2]?=some (.i32 0))
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.StateDecodeRaw.flagGuard++discarded))) (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=emptyBlockFrame frame stack.size code
  have branch:=wp_br_if_block_nonzero cfg fuel rest (paid s op 2) limits stack frame callers code discarded 1 post (by decide)
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using hnext)
  have test:=wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 1) limits stack f callers (.br_if 0::discarded) 0 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[Numeric.bool,beq_self_eq_true,ite_true,paid,op,f] using branch)
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack f callers (.i32_eqz::.br_if 0::discarded) 2 (.i32 0) post h2
    (hc.mono (by dsimp[op];omega)) test
  simpa only[WNear.Binary.StateDecodeRaw.flagGuard,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,f,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get

def arguments769Code : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.local_get 4,.local_get 1]
theorem wp_arguments769 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch size : UInt32) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 1)) (h4 : frame.locals[4]?=some (.i32 size))
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (scratch+16))).push (.i32 size)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (arguments769Code++code))) (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have one:=wp_local_get cfg fuel rest (paid s op 4) limits ((stack.push (.i32 (scratch+16))).push (.i32 size)) frame callers code 1 (.i32 1) post h1
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have sz:=wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (scratch+16))) frame callers (.local_get 1::code) 4 (.i32 size) post h4
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) one
  have add:=wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.local_get 4::.local_get 1::code) scratch 16 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) sz
  have sixteen:=wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 4::.local_get 1::code) 16 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_const 16::.i32_binop .add::.local_get 4::.local_get 1::code) 3 (.i32 scratch) post h3
    (hc.mono (by dsimp[op];omega)) sixteen
  simpa only[arguments769Code,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeRaw
