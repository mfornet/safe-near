import Proofs.AllocateVectorPhases
import NearVM.MeteredNumericRules

/-! Both686 conditionals fall through only after their actual nonzero test. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode
theorem wp_nonzero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (index depth : Nat) (value : UInt32) (post : Post)
    (hl : frame.locals[index]?=some (.i32 value)) (hn : value≠0)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get index::.i32_eqz::.br_if depth::code))) (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have branch := wp_br_if_zero cfg fuel rest (paid s op 2) limits stack frame callers code depth post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hnext
  have eqz := wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers (.br_if depth::code) value post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [Numeric.bool,show (value==0)=false from beq_eq_false_iff_ne.mpr hn,Bool.false_eq_true,ite_false,paid,op] using branch)
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers (.i32_eqz::.br_if depth::code)
    index (.i32 value) post hl (hc.mono (by dsimp [op];omega)) eqz
  have ce : cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [ce,Nat.add_assoc,Nat.reduceAdd] using get

end WNear.Proofs.AllocateVector
