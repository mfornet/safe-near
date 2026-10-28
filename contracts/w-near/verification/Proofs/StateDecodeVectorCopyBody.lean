import Proofs.StateDecodeVectorCopySuffix
import Proofs.StateDecodeVectorCopyCode
import Proofs.StateDecodeVectorResult

/-! Actual374 normal composition, including actual373 and the real951 loop. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode StateDecodeVector.callAfter
private theorem paid_modules (s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs (s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems (s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals (s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_body (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(a581 a236:Nat)(post:Post)
    (hn:Native p)(hcode:Code s frame.inst p a581 a236)(ha:p.allocator=1074896)
    (h0:frame.locals[0]?=some (.i32 p.outVector))(h1:frame.locals[1]?=some (.i32 p.source))(h2:frame.locals[2]?=some (.i32 p.size))
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.globalVector)(hv:p.globalVector.value=.i32 p.spVector)
    (hd:callers.length+9<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnxt:WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeVector.copyBody++code)))
      (bodyCost p*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let suffix:=argumentsCode++(.call 951::finishCode++code)
  let cost:=(18*p.size.toNat+25)*op+rest
  have c2:(vectorBefore s op).host.gas.Credits (620*op+cost):=paid_credits s op 2 _ (hc.mono (by dsimp[bodyCost,cost,op];simp only[Nat.add_mul];omega))
  have cv:(vectorAfter cfg s p).host.gas.Credits cost:=StateDecodeVector.callAfter_credits cfg (vectorBefore s op) p.toVector cost c2
  have vm:(vectorBefore s op).mems[p.memoryIndex]?=some p.memory:=by rw[vectorBefore,paid_mems];exact hm
  have vg:(vectorBefore s op).globals[p.globalIndex]?=some p.globalVector:=by rw[vectorBefore,paid_globals];exact hg
  have am:(vectorAfter cfg s p).mems[p.memoryIndex]?=some (StateDecodeVector.finalMemory p.toVector):=StateDecodeVector.callAfter_memory cfg (vectorBefore s op) p.toVector hn.vector vm
  have af:=StateDecodeVector.callAfter_fields cfg (vectorBefore s op) p.toVector
  have module:(vectorAfter cfg s p).modules[frame.inst]?=some p.mi:=by
    change (StateDecodeVector.callAfter cfg (vectorBefore s op) p.toVector).modules[frame.inst]?=some p.mi
    rw[af.2.1,vectorBefore,paid_modules];exact hcode.vector.raw.record.allocation.search.module
  have fn:(vectorAfter cfg s p).funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function):=by
    change (StateDecodeVector.callAfter cfg (vectorBefore s op) p.toVector).funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function)
    rw[af.1,vectorBefore,paid_funcs];exact hcode.function951
  have bounds:=copy_bounds p hn
  have ptr:readI32 (StateDecodeVector.finalMemory p.toVector) p.outVector.toNat=pointer p:=StateDecodeVector.finalMemory_pointer p.toVector hn.vector
  have outBound:p.outVector.toNat+12≤(StateDecodeVector.finalMemory p.toVector).byteSize:=by rw[bounds.2.1];exact hn.vector.outBound
  have dest:(readI32 (StateDecodeVector.finalMemory p.toVector) p.outVector.toNat).toNat+p.size.toNat≤(StateDecodeVector.finalMemory p.toVector).byteSize:=by rw[ptr];exact bounds.2.2.2.2.1
  have suffixNext:WP cfg fuel (.next (atCode (suffixAfter (vectorAfter cfg s p) op p.memoryIndex (StateDecodeVector.finalMemory p.toVector) p.outVector p.source p.size) limits base.toArray frame callers code)) rest post:=by
    simpa only[suffixAfter,after,copied,copyArguments,copiedMemory,ptr,op] using hnxt
  have suffixWP:=wp_suffix cfg fuel rest (vectorAfter cfg s p) limits base frame callers code p.outVector p.source p.size p.mi p.memoryIndex p.address951 (StateDecodeVector.finalMemory p.toVector) post
    h0 h1 h2 module hcode.vector.raw.record.allocation.search.memoryIndex am hcode.index951 fn bounds.1 bounds.2.2.1 outBound bounds.2.2.2.2.2.1 bounds.2.2.2.1 dest (by omega) cv suffixNext
  have hcVector:=vector_code s op frame.inst p a581 a236 hcode
  have func:(vectorBefore s op).funcs[p.address373]?=some (.wasm WNear.Binary.StateDecodeVector.signature frame.inst WNear.Binary.StateDecodeVector.function):=by rw[vectorBefore,paid_funcs];exact hcode.function373
  have callee:=StateDecodeVector.wp_call cfg (fuel+(17*p.size.toNat+20)) cost (vectorBefore s op) limits base frame callers suffix p.toVector a581 a236 p.address373 post
    hn.vector hcVector ha vm vg hv hcode.index373 func hd c2 suffixWP
  have arr:(base++[Value.i32 p.outVector,.i32 p.size]).toArray=(base.toArray.push (.i32 p.outVector)).push (.i32 p.size):=by apply Array.toList_inj.mp;simp
  have ready:WP cfg (fuel+(17*p.size.toNat+515)) (.next (atCode (vectorBefore s op) limits ((base.toArray.push (.i32 p.outVector)).push (.i32 p.size)) frame callers (.call 373::suffix)))
    ((18*p.size.toNat+645)*op+rest) post:=by
    simpa only[arr,show fuel+(17*p.size.toNat+20)+495=fuel+(17*p.size.toNat+515) by omega,
      show 620*cfg.regularOpCost+cost=(18*p.size.toNat+645)*op+rest by dsimp[cost,op];simp only[Nat.add_mul];omega] using callee
  have c1:=paid_credits s op 1 ((18*p.size.toNat+646)*op+rest) (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega))
  have get2:=wp_local_get cfg (fuel+(17*p.size.toNat+515)) ((18*p.size.toNat+645)*op+rest) (paid s op 1) limits (base.toArray.push (.i32 p.outVector)) frame callers (.call 373::suffix) 2 (.i32 p.size) post h2 (c1.mono (by simp only[Nat.add_mul];omega)) ready
  have getNext:WP cfg (fuel+(17*p.size.toNat+516)) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 p.outVector)) frame callers (.local_get 2::.call 373::suffix))) ((18*p.size.toNat+646)*op+rest) post:=by
    simpa only[show fuel+(17*p.size.toNat+515)+1=fuel+(17*p.size.toNat+516) by omega,
      show cfg.regularOpCost+((18*p.size.toNat+645)*op+rest)=(18*p.size.toNat+646)*op+rest by dsimp[op];simp only[Nat.add_mul];omega] using get2
  have get0:=wp_local_get cfg (fuel+(17*p.size.toNat+516)) ((18*p.size.toNat+646)*op+rest) s limits base.toArray frame callers (.local_get 2::.call 373::suffix) 0 (.i32 p.outVector) post h0 (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega)) getNext
  simpa only[WNear.Binary.StateDecodeVector.copyBody,suffix,argumentsCode,finishCode,List.cons_append,List.nil_append,bodyCost,bodySteps,
    show fuel+(17*p.size.toNat+516)+1=fuel+(17*p.size.toNat+517) by omega,
    show cfg.regularOpCost+((18*p.size.toNat+646)*op+rest)=(18*p.size.toNat+647)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using get0
end WNear.Proofs.StateDecodeVectorCopy
