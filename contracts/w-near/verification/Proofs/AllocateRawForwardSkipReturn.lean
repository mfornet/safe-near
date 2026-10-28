import Proofs.AllocateRawForwardSkipCall
import Proofs.ValueReturnLazyReturn

/-! Actual310 forwarding body, including its explicit normal return. -/
namespace WNear.Proofs.AllocateRawForwardSkip
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode callAfter236

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem wp_body310 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address581 address236 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.size)) (h1 : frame.locals[1]?=some (.i32 1))
    (hs : 3≤frame.locals.size) (harity : frame.arity=1) (hheight : frame.height=base.length)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi581 : p.mi.funcAddrs[581]?=some address581)
    (hf581 : s.funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature frame.inst WNear.Binary.Allocate.function))
    (hi236 : p.mi.funcAddrs[236]?=some address236)
    (hf236 : s.funcs[address236]?=some (.wasm WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function236))
    (hd : callers.length+5<limits.maxCallDepth)
    (hc : s.host.gas.Credits (cost310 p*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after310 cfg s p) limits
      (base++[Value.i32 (AllocatePositiveSkip.result p)]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+steps310 p) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateRawForward.body310++code))) (cost310 p*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let called := called236 cfg s p
  let result := AllocatePositiveSkip.result p
  let f : CallFrame := {frame with locals:=frame.locals.set! 2 (.i32 result)}
  have cc : called.host.gas.Credits (3*op+rest) := callAfter236_credits cfg (paid s op 2) p (3*op+rest)
    (paid_credits s op 2 _ (hc.mono (by simp only [cost310,Nat.add_mul,op];omega)))
  have f2 : f.locals[2]?=some (.i32 result) := by simp [f,show 2<frame.locals.size by omega]
  have aa : f.arity=[Value.i32 result].length := by simp only [f,List.length_cons,List.length_nil,Nat.reduceAdd];exact harity
  have hh : f.height=base.length := hheight
  have rn : WP cfg fuel (.next (atCode (chargedStore (paid called op 2) op) limits
      (base++[Value.i32 result]).toArray caller callers caller.code)) rest post := by
    simpa only [after310,called,result,paid,op] using hnext
  have ret := ValueReturnLazyLookup.wp_return_wasm cfg fuel rest (paid called op 2) limits base [.i32 result] f caller callers code post aa.symm hh
    (paid_credits called op 2 _ (cc.mono (by omega))) rn
  have arr : (base++[Value.i32 result]).toArray=base.toArray.push (.i32 result) := by apply Array.toList_inj.mp;simp
  have gn : WP cfg (fuel+1) (.next (atCode (chargedStore (paid called op 1) op) limits (base.toArray.push (.i32 result)) f
      (caller::callers) (.return::code))) (op+rest) post := by
    simpa only [arr,paid,op] using ret
  have get := wp_local_get cfg (fuel+1) (op+rest) (paid called op 1) limits base.toArray f (caller::callers)
    (.return::code) 2 (.i32 result) post f2 (paid_credits called op 1 _ (cc.mono (by omega))) gn
  have sn : WP cfg (fuel+2) (.next (atCode (chargedStore called op) limits base.toArray f (caller::callers)
      (.local_get 2::.return::code))) (op+(op+rest)) post := get
  have set := wp_local_set cfg (fuel+2) (op+(op+rest)) called limits base.toArray frame (caller::callers)
    (.local_get 2::.return::code) 2 (.i32 result) post (cc.mono (by omega)) sn
  have cn : WP cfg (fuel+3) (.next (atCode (callAfter236 cfg (paid s op 2) p) limits
      (base++[Value.i32 (AllocatePositiveSkip.result p)]).toArray frame (caller::callers)
      (.local_set 2::.local_get 2::.return::code))) (3*op+rest) post := by
    simpa only [called,called236,result,arr,show cfg.regularOpCost+(op+(op+rest))=3*op+rest by dsimp [op];omega] using set
  have cd := hcode.paid s op 2 frame.inst p
  have mm : (paid s op 2).mems[p.memoryIndex]?=some p.memory := by rw [mems_paid];exact hm
  have gg : (paid s op 2).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  have ff581 : (paid s op 2).funcs[address581]?=some (.wasm WNear.Binary.Allocate.signature frame.inst WNear.Binary.Allocate.function) := by rw [funcs_paid];exact hf581
  have ff236 : (paid s op 2).funcs[address236]?=some (.wasm WNear.Binary.AllocateRawForward.signature frame.inst WNear.Binary.AllocateRawForward.function236) := by rw [funcs_paid];exact hf236
  have call := wp_call236 cfg (fuel+3) (3*op+rest) (paid s op 2) limits base frame (caller::callers)
    (.local_set 2::.local_get 2::.return::code) p address581 address236 post hn cd ha mm gg hv hi581 ff581 hi236 ff236
    (by simpa only [List.length_cons] using hd)
    (paid_credits s op 2 _ (hc.mono (by simp only [cost310,Nat.add_mul,op];omega))) cn
  have arg : (base++[Value.i32 p.size,.i32 1]).toArray=(base.toArray.push (.i32 p.size)).push (.i32 1) := by apply Array.toList_inj.mp;simp
  have callNext : WP cfg (fuel+steps236 p+5) (.next (atCode (paid s op 2) limits
      ((base.toArray.push (.i32 p.size)).push (.i32 1)) frame (caller::callers)
      (.call 236::.local_set 2::.local_get 2::.return::code))) ((cost236 p+10)*op+(3*op+rest)) post := by
    have fe : (fuel+3)+steps236 p+2=fuel+steps236 p+5 := by omega
    simpa only [arg,op,fe] using call
  have g1 := wp_local_get cfg (fuel+steps236 p+5) _ (paid s op 1) limits (base.toArray.push (.i32 p.size)) frame (caller::callers)
    (.call 236::.local_set 2::.local_get 2::.return::code) 1 (.i32 1) post h1
    (paid_credits s op 1 _ (hc.mono (by simp only [cost310,Nat.add_mul,op];omega))) callNext
  have g0 := wp_local_get cfg (fuel+steps236 p+6) _ s limits base.toArray frame (caller::callers)
    (.local_get 1::.call 236::.local_set 2::.local_get 2::.return::code) 0 (.i32 p.size) post h0
    (hc.mono (by simp only [cost310,Nat.add_mul,op];omega)) g1
  have ce : cfg.regularOpCost+(cfg.regularOpCost+((cost236 p+10)*op+(3*op+rest)))=cost310 p*cfg.regularOpCost+rest := by
    simp only [cost310,Nat.add_mul,op];omega
  rw [ce] at g0
  simpa only [steps310,Nat.add_assoc,Nat.reduceAdd,WNear.Binary.AllocateRawForward.body310,List.cons_append,List.nil_append] using g0
end WNear.Proofs.AllocateRawForwardSkip
