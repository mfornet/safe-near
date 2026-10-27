import Proofs.AllocateZeroedTail
import Proofs.AllocatePositivePayload

/-! Full actual f153 body on the positive alignment-one directly-fitting path. -/
namespace WNear.Proofs.AllocateZeroed
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode allocated checked fillArguments filled after AllocatePositive.callAfter tailAfter tailFilled
set_option maxRecDepth 16384

 theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.allocator)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 3≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits
      (base++[Value.i32 (result p)]).toArray (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateZeroed.body++code)))
      (bodyCost p*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame base.length (.local_get 0::code)
  let a := arguments s op
  let r := result p
  let tailCost := (ZeroFill.bodyCost p.size+19)*op+rest
  have ca : a.host.gas.Credits (358*op+tailCost) := by
    apply paid_credits s op 3
    exact hc.mono (by simp only [bodyCost,op,Nat.add_mul,tailCost];omega)
  have cr := AllocatePositive.callAfter_credits a op tailCost p.toLayout ca
  have acode : Code a frame.inst p := hcode.paid s op 3 frame.inst p
  have am : a.mems[p.memoryIndex]?=some p.memory := hm
  have ag : a.globals[p.globalIndex]?=some p.global := hg
  have fields := AllocatePositive.callAfter_fields a op p.toLayout
  have module : (allocated s op p).modules[frame.inst]?=some p.mi := by
    rw [allocated,fields.2.1]
    exact acode.positive.search.module
  have fillFn : (allocated s op p).funcs[p.fillAddress]?=some (.wasm WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function) := by
    rw [allocated,fields.1]
    exact acode.fillFunction
  have memory : (allocated s op p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
    simpa only [allocated,a,allocatedMemory] using AllocatePositive.callAfter_memory a op p.toLayout am
  have postMemory := AllocatePositive.finalMemory_spec p.toLayout hn
  have nonzero := (AllocatePositive.result_nonzero_and_span p.toLayout hn).1
  have next : WP cfg fuel (.next (atCode (tailAfter (allocated s op p) op p.memoryIndex (allocatedMemory p) r p.size) limits
      (base++[Value.i32 r]).toArray (tailFrame frame r) callers code)) rest post := by
    simpa only [tailAfter,tailFilled,after,filled,fillArguments,checked,resultFrame,tailFrame,r,op] using hnext
  have tail := wp_tail cfg fuel rest (allocated s op p) limits base frame callers code r p.size p.mi p.fillAddress p.memoryIndex
    (allocatedMemory p) post h1 (by omega) module acode.fillIndex fillFn acode.positive.search.memoryIndex memory
    nonzero postMemory.1 (AllocatePositive.result_size_span p.toLayout hn) (AllocatePositive.result_width p.toLayout hn) (by omega) (by simpa only [allocated,a,tailCost,op] using cr) next
  have callNext : WP cfg (fuel+ZeroFill.bodySteps p.size+11) (.next (atCode (AllocatePositive.callAfter a op p.toLayout) limits
      (base++[Value.i32 (AllocatePositive.result p.toLayout)]).toArray bf callers WNear.Binary.AllocateZeroed.fill)) tailCost post := by
    simpa only [allocated,a,bf,r,result,op] using tail
  have call := AllocatePositive.wp_call cfg (fuel+ZeroFill.bodySteps p.size+11) tailCost a limits base bf callers
    WNear.Binary.AllocateZeroed.fill p.toLayout p.allocateAddress post hn acode.positive am ag hv acode.allocateIndex acode.allocateFunction hd ca callNext
  have callCost : 358*cfg.regularOpCost+tailCost=(ZeroFill.bodyCost p.size+377)*op+rest := by simp only [tailCost,op,Nat.add_mul];omega
  have arr3 : (base++[Value.i32 p.allocator,.i32 p.size,.i32 1]).toArray=((base.toArray.push (.i32 p.allocator)).push (.i32 p.size)).push (.i32 1) := by apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+ZeroFill.bodySteps p.size+310) (.next (atCode (paid s op 3) limits
      (((base.toArray.push (.i32 p.allocator)).push (.i32 p.size)).push (.i32 1)) bf callers (.call 581::WNear.Binary.AllocateZeroed.fill)))
      ((ZeroFill.bodyCost p.size+377)*op+rest) post := by
    simpa only [a,arguments,callCost,arr3,Nat.add_assoc,Nat.reduceAdd] using call
  have get2 := wp_local_get cfg (fuel+ZeroFill.bodySteps p.size+310) ((ZeroFill.bodyCost p.size+377)*op+rest) (paid s op 2) limits
    ((base.toArray.push (.i32 p.allocator)).push (.i32 p.size)) bf callers (.call 581::WNear.Binary.AllocateZeroed.fill) 2 (.i32 1) post h2
    (paid_credits s op 2 _ (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega))) (by simpa only [paid,op] using cn)
  have get1 := wp_local_get cfg (fuel+ZeroFill.bodySteps p.size+311) (op+((ZeroFill.bodyCost p.size+377)*op+rest)) (paid s op 1) limits
    (base.toArray.push (.i32 p.allocator)) bf callers (.local_get 2::.call 581::WNear.Binary.AllocateZeroed.fill) 1 (.i32 p.size) post h1
    (paid_credits s op 1 _ (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega)))
    (by simpa only [Nat.add_assoc,Nat.reduceAdd,op,paid] using get2)
  have get0 := wp_local_get cfg (fuel+ZeroFill.bodySteps p.size+312) (op+(op+((ZeroFill.bodyCost p.size+377)*op+rest))) s limits base.toArray bf callers
    (.local_get 1::.local_get 2::.call 581::WNear.Binary.AllocateZeroed.fill) 0 (.i32 p.allocator) post h0
    (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega)) (by simpa only [Nat.add_assoc,Nat.reduceAdd,op,paid] using get1)
  have inner : WP cfg (fuel+ZeroFill.bodySteps p.size+313) (.next (atCode s limits base.toArray bf callers WNear.Binary.AllocateZeroed.guarded))
      (bodyCost p*cfg.regularOpCost+rest) post := by
    have cost : cfg.regularOpCost+(op+(op+((ZeroFill.bodyCost p.size+377)*op+rest)))=bodyCost p*cfg.regularOpCost+rest := by simp only [bodyCost,op,Nat.add_mul];omega
    simpa only [WNear.Binary.AllocateZeroed.guarded,WNear.Binary.AllocateZeroed.arguments,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,cost] using get0
  have block := wp_block_empty cfg (fuel+ZeroFill.bodySteps p.size+313) (bodyCost p*cfg.regularOpCost+rest) s limits base.toArray frame callers
    WNear.Binary.AllocateZeroed.guarded (.local_get 0::code) post hc (by simpa only [bf,List.size_toArray] using inner)
  have steps : fuel+ZeroFill.bodySteps p.size+313+1=fuel+bodySteps p := by simp only [bodySteps];omega
  simpa only [WNear.Binary.AllocateZeroed.body,List.cons_append,List.nil_append,steps] using block

end WNear.Proofs.AllocateZeroed
