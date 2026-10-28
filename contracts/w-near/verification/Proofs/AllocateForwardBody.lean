import Binary.AllocateForward
import Proofs.AllocateZeroedResources

/-! Actual239 forwarding body, selecting positive alignment-one zeroed allocation.
The callee is proved from original heap and code resources. -/
namespace WNear.Proofs.AllocateForward
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
abbrev Layout := AllocateZeroed.Layout
abbrev Native := AllocateZeroed.Native
abbrev Code := AllocateZeroed.Code

def after239 (s : Store NearState) (op : Nat) (p : Layout) :=
  AllocateZeroed.callAfter (paid s op 3) op p
def cost239 (p : Layout) := AllocateZeroed.bodyCost p+14
def steps239 (p : Layout) := AllocateZeroed.bodySteps p+5

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem after239_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (cost239 p*op+rest)) : (after239 s op p).host.gas.Credits rest := by
  apply AllocateZeroed.callAfter_credits
  exact paid_credits s op 3 _ (hc.mono (by simp only [cost239,Nat.add_mul];omega))

set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after239 AllocateZeroed.callAfter

theorem wp_body239 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address153 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p) (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.size)) (h1 : frame.locals[1]?=some (.i32 1))
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hi : p.mi.funcAddrs[153]?=some address153)
    (hf : s.funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function))
    (hd : callers.length+4<limits.maxCallDepth)
    (hc : s.host.gas.Credits (cost239 p*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after239 s cfg.regularOpCost p) limits
      (base++[Value.i32 (AllocateZeroed.result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+steps239 p) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.AllocateForward.body239++code))) (cost239 p*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let c := (AllocateZeroed.bodyCost p+11)*op+rest
  have cc : (paid s op 3).host.gas.Credits c := paid_credits s op 3 _
    (hc.mono (by simp only [cost239,Nat.add_mul,c,op];omega))
  have cd := hcode.paid s op 3 frame.inst p
  have mm : (paid s op 3).mems[p.memoryIndex]?=some p.memory := by rw [mems_paid];exact hm
  have gg : (paid s op 3).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  have ff : (paid s op 3).funcs[address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature frame.inst WNear.Binary.AllocateZeroed.function) := by
    rw [funcs_paid];exact hf
  have cn : WP cfg fuel (.next (atCode (AllocateZeroed.callAfter (paid s op 3) op p) limits
      (base++[Value.i32 (AllocateZeroed.result p)]).toArray frame callers code)) rest post := by
    simpa only [after239,op] using hnext
  have call := AllocateZeroed.wp_call cfg fuel rest (paid s op 3) limits base frame callers code p address153 post hn cd mm gg hv hi ff hd cc cn
  have args : (base++[Value.i32 p.allocator,.i32 p.size,.i32 1]).toArray=
      ((base.toArray.push (.i32 1074896)).push (.i32 p.size)).push (.i32 1) := by
    apply Array.toList_inj.mp
    simp [ha]
  have callNext : WP cfg (fuel+AllocateZeroed.bodySteps p+2) (.next (atCode (paid s op 3) limits
      (((base.toArray.push (.i32 1074896)).push (.i32 p.size)).push (.i32 1)) frame callers (.call 153::code))) c post := by
    simpa only [args,c,op] using call
  have g1 := wp_local_get cfg (fuel+AllocateZeroed.bodySteps p+2) c (paid s op 2) limits
    ((base.toArray.push (.i32 1074896)).push (.i32 p.size)) frame callers (.call 153::code) 1 (.i32 1) post h1
    (paid_credits s op 2 _ (hc.mono (by simp only [cost239,Nat.add_mul,c,op];omega))) callNext
  have g0 := wp_local_get cfg (fuel+AllocateZeroed.bodySteps p+3) (op+c) (paid s op 1) limits
    (base.toArray.push (.i32 1074896)) frame callers (.local_get 1::.call 153::code) 0 (.i32 p.size) post h0
    (paid_credits s op 1 _ (hc.mono (by simp only [cost239,Nat.add_mul,c,op];omega))) g1
  have k := wp_i32_const cfg (fuel+AllocateZeroed.bodySteps p+4) (op+(op+c)) s limits base.toArray frame callers
    (.local_get 0::.local_get 1::.call 153::code) 1074896 post
    (hc.mono (by simp only [cost239,Nat.add_mul,c,op];omega)) g0
  have ce : cfg.regularOpCost+(op+(op+c))=cost239 p*cfg.regularOpCost+rest := by
    simp only [cost239,c,op,Nat.add_mul];omega
  simpa only [ce,steps239,Nat.add_assoc,Nat.reduceAdd,WNear.Binary.AllocateForward.body239,List.cons_append,List.nil_append] using k
end WNear.Proofs.AllocateForward
