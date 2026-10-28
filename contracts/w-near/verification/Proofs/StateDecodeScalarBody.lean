import Proofs.StateDecodeScalarTail

/-! Complete deployed accepted f372/f371 bodies, including all nested calls and
explicit return. Every resource hypothesis refers to the original callee state. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode accepted after

theorem wp_body (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native wide p) (hcode : Code wide s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global)
    (hv : p.global.value=.i32 p.sp) (h0 : frame.locals[0]?=some (.i32 p.out))
    (h1 : frame.locals[1]?=some (.i32 p.slice)) (hs : (if wide then 7 else 6)≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length) (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost wide*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after wide cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+bodySteps wide) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.StateDecodeScalar.body wide++code))) (bodyCost wide*cfg.regularOpCost+rest) post := by
  have tail:=wp_tail wide cfg fuel rest s limits base frame caller callers code p post hn hcode hm hg h0 h1 hs ha hh hd hc hnext
  have first:=wp_prefix wide cfg (fuel+(if wide then 59 else 51)) ((if wide then 67 else 59)*cfg.regularOpCost+rest)
    s limits base frame (caller::callers) code p post hn hcode hm hg hv h1
    (by cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hs <;> omega)
    (by simpa only[List.length_cons] using hd)
    (hc.mono (by cases wide <;> simp only [bodyCost,ite_true,Bool.false_eq_true,ite_false] <;> omega)) tail
  cases wide <;> simpa only [bodyCost,bodySteps,ite_true,Bool.false_eq_true,ite_false,Nat.add_assoc,Nat.reduceAdd,
    show 87*cfg.regularOpCost+(67*cfg.regularOpCost+rest)=154*cfg.regularOpCost+rest by omega,
    show 79*cfg.regularOpCost+(59*cfg.regularOpCost+rest)=138*cfg.regularOpCost+rest by omega] using first
end WNear.Proofs.StateDecodeScalar
