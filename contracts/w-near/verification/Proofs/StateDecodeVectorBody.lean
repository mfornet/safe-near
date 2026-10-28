import Proofs.StateDecodeVectorFinalFrame
import Proofs.StateDecodeVectorMemory
import Proofs.StateDecodeRawCall

/-! Actual373 normal composition: real767 allocation and thirteen scalar suffix
instructions, with only original native/code resources. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode StateDecodeRaw.callAfterRaw
private theorem funcs_paid (s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem funcs_global (s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).funcs=s.funcs:=rfl
private theorem globals_paid (s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_body (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(a581 a236:Nat)(post:Post)
    (hn:Native p)(hcode:Code s frame.inst p a581 a236)(ha:p.allocator=1074896)
    (h0:frame.locals[0]?=some (.i32 p.outVector))(h1:frame.locals[1]?=some (.i32 p.size))(hsize:4≤frame.locals.size)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.globalVector)(hv:p.globalVector.value=.i32 p.spVector)
    (hd:callers.length+8<limits.maxCallDepth)(hc:s.host.gas.Credits (608*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray (cachedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+493) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeVector.body++code)))
      (608*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=reservedFrame frame p
  let suffix:=WNear.Binary.StateDecodeVector.cache++WNear.Binary.StateDecodeVector.output++WNear.Binary.StateDecodeVector.restore++code
  have cr:(reserved s op p).host.gas.Credits (603*op+rest):=paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  have ca:(arguments s op p).host.gas.Credits (598*op+rest):=paid_credits (reserved s op p) op 5 _ (cr.mono (by omega))
  have caRaw:(arguments s op p).host.gas.Credits (585*cfg.regularOpCost+(13*op+rest)):=by
    simpa only[show 585*cfg.regularOpCost+(13*op+rest)=598*op+rest by dsimp[op];omega] using ca
  have cal:(allocated cfg s p).host.gas.Credits (13*op+rest):=
    StateDecodeRaw.callAfterRaw_credits cfg (arguments s op p) p.toRaw _ caRaw
  have hcargs:=arguments_raw_code s op frame.inst p a581 a236 hcode
  have f0:f.locals[0]?=some (.i32 p.outVector):=by simp[f,reservedFrame,Array.set!,h0]
  have f1:f.locals[1]?=some (.i32 p.size):=by simp[f,reservedFrame,Array.set!,h1]
  have f2:f.locals[2]?=some (.i32 (scratch p)):=by simp[f,reservedFrame,Array.set!,show 2<frame.locals.size by omega]
  have fs:4≤f.locals.size:=by simpa only[f,reservedFrame,Array.size_set!] using hsize
  have nums:=stack_numbers p hn
  have spec:=allocated_spec p hn
  have am:=allocated_memory cfg s p hn hm
  have ai:=StateDecodeRaw.callAfterRaw_fields cfg (arguments s op p) p.toRaw
  have module:(allocated cfg s p).modules[f.inst]?=some p.mi:=by
    change (StateDecodeRaw.callAfterRaw cfg (arguments s op p) p.toRaw).modules[frame.inst]?=some p.mi
    rw[ai.2.1]
    exact hcargs.record.allocation.search.module
  have ag:(allocated cfg s p).globals[p.globalIndex]?=some p.globalRaw:=by
    rw[allocated_globals cfg s p hn hg]
    simpa only[arguments,globals_paid] using arguments_global s op p hn hg
  have sb:(scratch p).toNat+16≤(memoryAllocated p).byteSize:=by rw[spec.2.1];exact nums.2.2.2.1
  have ob:p.outVector.toNat+12≤(memoryAllocated p).byteSize:=by rw[spec.2.1];exact hn.outBound
  have tailNext:WP cfg fuel (.next (atCode (tailAfter (allocated cfg s p) op p.memoryIndex p.globalIndex (memoryAllocated p) p.outVector (scratch p))
      limits base.toArray (tailFrame f (memoryAllocated p) (scratch p)) callers code)) rest post:=by
    simpa only[after_eq,cachedFrame,tailFrame,packed,f,op] using hnext
  have tail:=wp_tail cfg fuel rest (allocated cfg s p) limits base.toArray f callers code p.outVector (scratch p)
    p.mi p.memoryIndex p.globalIndex p.globalRaw (memoryAllocated p) post f0 f2 fs module hcargs.record.allocation.search.memoryIndex
    hcargs.record.allocation.globalIndex am ag spec.1 sb ob cal tailNext
  have argmem:=arguments_memory s op p hm
  have argglobal:=arguments_global s op p hn hg
  have argv:p.globalRaw.value=.i32 p.spRaw:=by rw[hn.childGlobal]
  have fi:(arguments s op p).funcs[p.address767]?=some (.wasm WNear.Binary.StateDecodeRaw.signature f.inst WNear.Binary.StateDecodeRaw.function767):=by
    simp only[arguments,reserved,funcs_paid,funcs_global]
    exact hcode.function767
  have call:=StateDecodeRaw.wp_callRaw cfg (fuel+13) (13*op+rest) (arguments s op p) limits base f callers suffix p.toRaw a581 a236 p.address767 post
    hn.raw hcargs ha argmem argglobal argv hcode.index767 fi hd caRaw tail
  have out:p.outRaw=scratch p+8:=by rw[hn.childOut,hn.childSP];rfl
  have arr:(base++[Value.i32 p.outRaw,.i32 p.size,.i32 p.flag]).toArray=
      ((base.toArray.push (.i32 (scratch p+8))).push (.i32 p.size)).push (.i32 0):=by
    apply Array.toList_inj.mp
    simp[out,hn.raw.flagZero]
  have argsNext:WP cfg (fuel+483) (.next (atCode (arguments s op p) limits
      (((base.toArray.push (.i32 (scratch p+8))).push (.i32 p.size)).push (.i32 0)) f callers (.call 767::suffix))) (598*op+rest) post:=by
    simpa only[arr,show fuel+13+470=fuel+483 by omega,show 585*cfg.regularOpCost+(13*op+rest)=598*op+rest by dsimp[op];omega] using call
  have args:=wp_arguments cfg (fuel+483) (598*op+rest) (reserved s op p) limits base.toArray f callers (.call 767::suffix)
    (scratch p) p.size post f2 f1 (cr.mono (by omega)) argsNext
  have rn:WP cfg (fuel+488) (.next (atCode (reserved s op p) limits base.toArray f callers (WNear.Binary.StateDecodeVector.arguments++(.call 767::suffix)))) (603*op+rest) post:=by
    simpa only[show 5*cfg.regularOpCost+(598*op+rest)=603*op+rest by dsimp[op];omega] using args
  have reserve:=InterfaceStack.wp_reserve cfg (fuel+488) (603*op+rest) s limits base.toArray frame callers
    (WNear.Binary.StateDecodeVector.arguments++(.call 767::suffix)) p.mi p.globalIndex p.globalVector p.spVector 2 16 post
    hcode.raw.record.allocation.search.module hcode.raw.record.allocation.globalIndex hg hv (hc.mono (by dsimp[op];omega)) rn
  simpa only[WNear.Binary.StateDecodeVector.body,WNear.Binary.StateDecodeVector.setup,suffix,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,
    show fuel+488+5=fuel+493 by omega,
    show 5*cfg.regularOpCost+(603*op+rest)=608*cfg.regularOpCost+rest by dsimp[op];omega] using reserve
end WNear.Proofs.StateDecodeVector
