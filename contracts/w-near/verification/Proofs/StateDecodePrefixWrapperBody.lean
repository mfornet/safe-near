import Proofs.StateDecodePrefixWrapperPhases
import Proofs.StateDecodePrefixWrapperTail
import Proofs.StateDecodePrefixFinalMemorySpec

/-! Full accepted315 uses the actual316 theorem, then its real branch/copy.
Original tag/descriptor separation is explicit because316 updates the slice
AFTER writing its output tag. Caller output aliases remain sequential. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode decoded after StateDecodePrefix.finalMemory

theorem tail_native(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q):Tail.Native (tailLayout p q):=by
  have shape:=StateDecodePrefix.finalMemory_spec p.toPrefix q hn.child hd.toAllocationDomain
  refine ⟨shape.1,?_,?_,?_⟩
  · change (StateDecodePrefix.finalMemory p.toPrefix q).byteSize≤2^32
    rw[shape.2.1];exact hn.child.memoryWidth
  · change (scratch p).toNat+16≤(StateDecodePrefix.finalMemory p.toPrefix q).byteSize
    rw[shape.2.1];exact child_scratch_bound p hn
  · change p.wrapperOut.toNat+16≤(StateDecodePrefix.finalMemory p.toPrefix q).byteSize
    rw[shape.2.1];exact hn.outputBound

theorem wp_body(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hcode:Code s frame.inst p)(hqcode:StateDecodeVectorCopy.Code s frame.inst q a581 a236)(ha:q.allocator=1074896)
    (hcallback:p.sp.toNat≤1057464+16)(hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (htagsep:p.out.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal)(hv:p.wrapperGlobal.value=.i32 p.wrapperSP)
    (h0:frame.locals[0]?=some (.i32 p.wrapperOut))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:4≤frame.locals.size)
    (hdepth:callers.length+11<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefixWrapper.body++code)))
      (bodyCost p*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=reservedFrame frame p
  let t:=tailLayout p q
  have fields:=decoded_fields cfg s p q
  have z:=StateDecodePrefix.finalMemory_tag0 p.toPrefix q hn.child hd htagsep
  rw[hn.childOut] at z
  have tail:=Tail.wp_tail cfg fuel rest (decoded cfg s p q) limits base.toArray f callers code t p.mi p.global post (tail_native p q hn hd)
    (by simp[f,reservedFrame,h0,t,tailLayout]) (by simp[f,reservedFrame,t,tailLayout,show 2<frame.locals.size by omega]) (by simpa only[f,reservedFrame,Array.size_set!] using hs)
    (by change (decoded cfg s p q).modules[frame.inst]?=some p.mi;rw[fields.2.1];exact hcode.child.module)
    hcode.child.memoryIndex (decoded_memory cfg s p q hn hd hm) hcode.child.globalIndex (decoded_global cfg s p q hn hd hg)
    (by change readI32 (StateDecodePrefix.finalMemory p.toPrefix q) (scratch p).toNat≠1;rw[z];decide)
    (decoded_credits cfg s p q (33*op+rest) hn hd (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega)))
    (by simpa only[after,finalFrame,f,t] using hnext)
  have start:=wp_prefix cfg (fuel+35) (33*op+rest) s limits base frame callers (Tail.codeTail++code) p q a581 a236 post hn hd hcode hqcode ha hcallback hsep hm hg hv h1 (by omega) hdepth
    (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega)) tail
  simpa only[WNear.Binary.StateDecodePrefixWrapper.body,Tail.codeTail,bodyCost,bodySteps,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show fuel+35+(17*(StateDecodePrefix.count p.toPrefix).toNat+734)=fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+769) by omega,
    show (18*(StateDecodePrefix.count p.toPrefix).toNat+927)*cfg.regularOpCost+(33*op+rest)=(18*(StateDecodePrefix.count p.toPrefix).toNat+960)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using start
end WNear.Proofs.StateDecodePrefixWrapper
