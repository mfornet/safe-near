import Proofs.AllocateZeroedRetryResources
import Proofs.AllocateRetryCall

/-! Full actual f153 body on the positive alignment-one growth-and-retry path. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode allocated after AllocateRetry.callAfter
open AllocateZeroed (tailAfter tailFrame wp_tail)
set_option maxRecDepth 16384

 theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.allocator)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 3≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hd : callers.length+4<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits
      (base++[Value.i32 (result p)]).toArray (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateZeroed.body++code)))
      (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame base.length (.local_get 0::code)
  let a := arguments s op
  let r := result p
  let tailCost := (ZeroFill.bodyCost p.size+19)*op+rest
  have ca : a.host.gas.Credits (603*op+fee cfg p+tailCost) := by
    apply paid_credits s op 3
    exact hc.mono (by simp only [bodyCost,op,Nat.add_mul,tailCost];omega)
  have cr := (allocated_gas cfg s p tailCost (hc.mono (by simp only [bodyCost,tailCost,Nat.add_mul,op];omega))).2.2
  have acode : Code a frame.inst p := hcode.paid s op 3 frame.inst p
  have am : a.mems[p.memoryIndex]?=some p.memory := hm
  have ag : a.globals[p.globalIndex]?=some p.global := hg
  have fields := allocated_fields cfg s p
  have module : (allocated cfg s p).modules[frame.inst]?=some p.mi := by
    rw [fields.2.1]
    exact hcode.retry.originalCode.search.module
  have fillFn : (allocated cfg s p).funcs[p.fillAddress]?=some (.wasm WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function) := by
    rw [fields.1]
    exact hcode.fillFunction
  have memory := allocated_memory cfg s p hm
  have postMemory := AllocateRetry.finalMemory_spec p.toRetry hn
  have nonzero := result_nonzero p hn
  have next : WP cfg fuel (.next (atCode (tailAfter (allocated cfg s p) op p.memoryIndex (allocatedMemory p) r p.size) limits
      (base++[Value.i32 r]).toArray (tailFrame frame r) callers code)) rest post := by
    simpa only [after,resultFrame,r,op] using hnext
  have tail := wp_tail cfg fuel rest (allocated cfg s p) limits base frame callers code r p.size p.mi p.fillAddress p.memoryIndex
    (allocatedMemory p) post h1 (by omega) module acode.fillIndex fillFn hcode.retry.originalCode.search.memoryIndex memory
    nonzero postMemory.1 (AllocateRetry.result_size_span p.toRetry hn) (AllocateRetry.result_width p.toRetry hn) (by omega) (by simpa only [tailCost,op] using cr) next
  have callNext : WP cfg (fuel+ZeroFill.bodySteps p.size+11) (.next (atCode (AllocateRetry.callAfter cfg a p.toRetry) limits
      (base++[Value.i32 (AllocateRetry.result p.toRetry)]).toArray bf callers WNear.Binary.AllocateZeroed.fill)) tailCost post := by
    simpa only [allocated,AllocateRetry.callAfter,AllocateRetry.entered,allocateEntered,a,bf,r,result,op] using tail
  have call := AllocateRetry.wp_call cfg (fuel+ZeroFill.bodySteps p.size+11) tailCost a limits base bf callers
    WNear.Binary.AllocateZeroed.fill p.toRetry p.allocateAddress post hn acode.retry am ag hv acode.allocateIndex acode.allocateFunction hd ca callNext
  have callCost : 603*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p.toRetry))+tailCost=(ZeroFill.bodyCost p.size+622)*op+fee cfg p+rest := by simp only [tailCost,op,Nat.add_mul,fee];omega
  rw [callCost] at call
  have arr3 : (base++[Value.i32 p.allocator,.i32 p.size,.i32 1]).toArray=((base.toArray.push (.i32 p.allocator)).push (.i32 p.size)).push (.i32 1) := by apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+ZeroFill.bodySteps p.size+502) (.next (atCode (paid s op 3) limits
      (((base.toArray.push (.i32 p.allocator)).push (.i32 p.size)).push (.i32 1)) bf callers (.call 581::WNear.Binary.AllocateZeroed.fill)))
      ((ZeroFill.bodyCost p.size+622)*op+fee cfg p+rest) post := by
    simpa only [a,arguments,arr3,Nat.add_assoc,Nat.reduceAdd] using call
  have get2 := wp_local_get cfg (fuel+ZeroFill.bodySteps p.size+502) ((ZeroFill.bodyCost p.size+622)*op+fee cfg p+rest) (paid s op 2) limits
    ((base.toArray.push (.i32 p.allocator)).push (.i32 p.size)) bf callers (.call 581::WNear.Binary.AllocateZeroed.fill) 2 (.i32 1) post h2
    (paid_credits s op 2 _ (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega))) (by simpa only [paid,op] using cn)
  have get1 := wp_local_get cfg (fuel+ZeroFill.bodySteps p.size+503) (op+((ZeroFill.bodyCost p.size+622)*op+fee cfg p+rest)) (paid s op 1) limits
    (base.toArray.push (.i32 p.allocator)) bf callers (.local_get 2::.call 581::WNear.Binary.AllocateZeroed.fill) 1 (.i32 p.size) post h1
    (paid_credits s op 1 _ (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega)))
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,op,paid] using get2)
  have get0 := wp_local_get cfg (fuel+ZeroFill.bodySteps p.size+504) (op+(op+((ZeroFill.bodyCost p.size+622)*op+fee cfg p+rest))) s limits base.toArray bf callers
    (.local_get 1::.local_get 2::.call 581::WNear.Binary.AllocateZeroed.fill) 0 (.i32 p.allocator) post h0
    (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega)) (by simpa only [Nat.add_assoc,Nat.reduceAdd,op,paid] using get1)
  have inner : WP cfg (fuel+ZeroFill.bodySteps p.size+505) (.next (atCode s limits base.toArray bf callers WNear.Binary.AllocateZeroed.guarded))
      (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
    have cost : cfg.regularOpCost+(op+(op+((ZeroFill.bodyCost p.size+622)*op+fee cfg p+rest)))=bodyCost p*cfg.regularOpCost+fee cfg p+rest := by simp only [bodyCost,op,Nat.add_mul];omega
    rw [cost] at get0
    simpa only [WNear.Binary.AllocateZeroed.guarded,WNear.Binary.AllocateZeroed.arguments,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using get0
  have block := wp_block_empty cfg (fuel+ZeroFill.bodySteps p.size+505) (bodyCost p*cfg.regularOpCost+fee cfg p+rest) s limits base.toArray frame callers
    WNear.Binary.AllocateZeroed.guarded (.local_get 0::code) post hc (by simpa only [bf,List.size_toArray] using inner)
  have steps : fuel+ZeroFill.bodySteps p.size+505+1=fuel+bodySteps p := by simp only [bodySteps];omega
  simpa only [WNear.Binary.AllocateZeroed.body,List.cons_append,List.nil_append,steps] using block

end WNear.Proofs.AllocateZeroedRetry
