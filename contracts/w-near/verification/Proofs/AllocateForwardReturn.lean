import Proofs.AllocateForwardCall
import Proofs.ValueReturnLazyReturn

/-! Actual313 forwarding body, including its explicit normal return. -/
namespace WNear.Proofs.AllocateForward
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode callAfter239

def called239 (s : Store NearState) (op : Nat) (p : Layout) := callAfter239 (paid s op 2) op p
def after313 (s : Store NearState) (op : Nat) (p : Layout) := paid (called239 s op p) op 3
def cost313 (p : Layout) := cost239 p+15
def steps313 (p : Layout) := steps239 p+7

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem after313_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (cost313 p*op+rest)) : (after313 s op p).host.gas.Credits rest := by
  apply paid_credits
  apply callAfter239_credits
  exact paid_credits s op 2 _ (hc.mono (by simp only [cost313,Nat.add_mul];omega))

theorem wp_body313 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address153 address239 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.size)) (h1 : frame.locals[1]?=some (.i32 1))
    (hs : 3≤frame.locals.size) (harity : frame.arity=1) (hheight : frame.height=base.length)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi153 : p.mi.funcAddrs[153]?=some address153)
    (hf153 : s.funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function))
    (hi239 : p.mi.funcAddrs[239]?=some address239)
    (hf239 : s.funcs[address239]?=some (.wasm WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function239))
    (hd : callers.length+6<limits.maxCallDepth)
    (hc : s.host.gas.Credits (cost313 p*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after313 s cfg.regularOpCost p) limits
      (base++[Value.i32 (AllocateZeroed.result p)]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+steps313 p) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateForward.body313++code))) (cost313 p*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let called := called239 s op p
  let result := AllocateZeroed.result p
  let f : CallFrame := {frame with locals:=frame.locals.set! 2 (.i32 result)}
  have cc : called.host.gas.Credits (3*op+rest) := callAfter239_credits (paid s op 2) op (3*op+rest) p
    (paid_credits s op 2 _ (hc.mono (by simp only [cost313,Nat.add_mul,op];omega)))
  have f2 : f.locals[2]?=some (.i32 result) := by simp [f,show 2<frame.locals.size by omega]
  have aa : f.arity=[Value.i32 result].length := by simp only [f,List.length_cons,List.length_nil,Nat.reduceAdd];exact harity
  have hh : f.height=base.length := hheight
  have rn : WP cfg fuel (.next (atCode (chargedStore (paid called op 2) op) limits
      (base++[Value.i32 result]).toArray caller callers caller.code)) rest post := by
    simpa only [after313,called,result,paid,op] using hnext
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
  have cn : WP cfg (fuel+3) (.next (atCode (callAfter239 (paid s op 2) op p) limits
      (base++[Value.i32 (AllocateZeroed.result p)]).toArray frame (caller::callers)
      (.local_set 2::.local_get 2::.return::code))) (3*op+rest) post := by
    simpa only [called,called239,result,arr,show cfg.regularOpCost+(op+(op+rest))=3*op+rest by dsimp [op];omega] using set
  have cd := hcode.paid s op 2 frame.inst p
  have mm : (paid s op 2).mems[p.memoryIndex]?=some p.memory := by rw [mems_paid];exact hm
  have gg : (paid s op 2).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  have ff153 : (paid s op 2).funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function) := by rw [funcs_paid];exact hf153
  have ff239 : (paid s op 2).funcs[address239]?=some (.wasm WNear.Binary.AllocateForward.signature frame.inst WNear.Binary.AllocateForward.function239) := by rw [funcs_paid];exact hf239
  have call := wp_call239 cfg (fuel+3) (3*op+rest) (paid s op 2) limits base frame (caller::callers)
    (.local_set 2::.local_get 2::.return::code) p address153 address239 post hn cd ha mm gg hv hi153 ff153 hi239 ff239
    (by simpa only [List.length_cons] using hd)
    (paid_credits s op 2 _ (hc.mono (by simp only [cost313,Nat.add_mul,op];omega))) cn
  have arg : (base++[Value.i32 p.size,.i32 1]).toArray=(base.toArray.push (.i32 p.size)).push (.i32 1) := by apply Array.toList_inj.mp;simp
  have callNext : WP cfg (fuel+steps239 p+5) (.next (atCode (paid s op 2) limits
      ((base.toArray.push (.i32 p.size)).push (.i32 1)) frame (caller::callers)
      (.call 239::.local_set 2::.local_get 2::.return::code))) ((cost239 p+10)*op+(3*op+rest)) post := by
    have fe : (fuel+3)+steps239 p+2=fuel+steps239 p+5 := by omega
    simpa only [arg,op,fe] using call
  have g1 := wp_local_get cfg (fuel+steps239 p+5) _ (paid s op 1) limits (base.toArray.push (.i32 p.size)) frame (caller::callers)
    (.call 239::.local_set 2::.local_get 2::.return::code) 1 (.i32 1) post h1
    (paid_credits s op 1 _ (hc.mono (by simp only [cost313,Nat.add_mul,op];omega))) callNext
  have g0 := wp_local_get cfg (fuel+steps239 p+6) _ s limits base.toArray frame (caller::callers)
    (.local_get 1::.call 239::.local_set 2::.local_get 2::.return::code) 0 (.i32 p.size) post h0
    (hc.mono (by simp only [cost313,Nat.add_mul,op];omega)) g1
  have ce : cfg.regularOpCost+(cfg.regularOpCost+((cost239 p+10)*op+(3*op+rest)))=cost313 p*cfg.regularOpCost+rest := by
    simp only [cost313,Nat.add_mul,op];omega
  simpa only [ce,steps313,Nat.add_assoc,Nat.reduceAdd,WNear.Binary.AllocateForward.body313,List.cons_append,List.nil_append] using g0
end WNear.Proofs.AllocateForward
