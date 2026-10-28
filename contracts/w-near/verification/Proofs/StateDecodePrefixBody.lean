import Proofs.StateDecodePrefixCopyCall
import Proofs.StateDecodePrefixTail
import Proofs.StateDecodePrefixGas
import Proofs.StateDecodePrefixFrame
import Proofs.StateDecodePrefixFinalMemoryFrame
import Proofs.StateDecodePrefixAllocationCode
import Proofs.StateDecodePrefixAfterAllocationReadback

/-! Full deployed316 accepted byte-vector decoding, including actual374
allocation/copy and the final descriptor drop. All domains refer to original
memory and code, never a future callee execution outcome. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] lengthMemory readI32 readI64
attribute [local irreducible] WP atCode allocationInput allocatedMemory droppedMemory takenPayloadMemory payloadPrefix copyArguments allocated dropped outputted after
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem enough_inst(frame:CallFrame)(p:Layout):(enoughPrefixFrame frame p).inst=frame.inst:=by
  simp only[enoughPrefixFrame,enoughFrame,countedPrefixFrame,countFrame,statusPrefixFrame,statusFrame,guardedPrefixFrame,AllocateVector.loadedFrame,reservedPrefixFrame]
private theorem exact374:WNear.Binary.f374=WNear.Binary.StateDecodeVector.copyFunction:=by kernel_rfl
private theorem labels_enough(frame:CallFrame)(height:Nat)(code:Expr)(p:Layout):
    enoughPrefixFrame (prefixLabels frame height code) p=
      Output.nested (enoughPrefixFrame frame p) height (WNear.Binary.StateDecodePrefix.restore++code)
        WNear.Binary.StateDecodePrefix.invalid WNear.Binary.StateDecodePrefix.short WNear.Binary.StateDecodePrefix.panic:=by
  simp only[enoughPrefixFrame,enoughFrame,countedPrefixFrame,countFrame,statusPrefixFrame,statusFrame,guardedPrefixFrame,AllocateVector.loadedFrame,reservedPrefixFrame,prefixLabels,Output.nested,emptyBlockFrame]

theorem wp_body (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p)
    (hqcode:StateDecodeVectorCopy.Code s frame.inst q a581 a236)(ha:q.allocator=1074896)
    (hcallback:p.sp.toNat≤1057464+16)(hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global)(hv:p.global.value=.i32 p.sp)
    (h0:frame.locals[0]?=some (.i32 p.out))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:6≤frame.locals.size)
    (hdepth:callers.length+10<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.body++code)))
      (bodyCost p*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let x:=allocationInput p q
  let e:=enoughPrefixFrame frame p
  let n:=enoughPrefixFrame (prefixLabels frame base.toArray.size code) p
  have el:=enoughPrefixFrame_locals frame p hs hn
  have e0:e.locals[0]?=some (.i32 p.out):=el.2.1.trans h0
  have e1:e.locals[1]?=some (.i32 p.slice):=el.2.2.1.trans h1
  have e2:e.locals[2]?=some (.i32 (scratch p)):=el.2.2.2.1
  have e3:e.locals[3]?=some (.i32 (count p)):=el.2.2.2.2.1
  have ei:e.inst=frame.inst:=enough_inst frame p
  have ni:n.inst=frame.inst:=enough_inst (prefixLabels frame base.toArray.size code) p
  have xm:x.memory=takenPayloadMemory p:=by unfold x allocationInput;rfl
  have xi:x.memoryIndex=p.memoryIndex:=by unfold x allocationInput;exact hd.memoryIndex
  have xg:x.globalIndex=p.globalIndex:=by unfold x allocationInput;exact hd.globalIndex
  have xv:x.globalVector={p.global with value:=.i32 (scratch p)}:=by unfold x allocationInput;exact hd.global
  have xsp:x.spVector=scratch p:=by unfold x allocationInput;exact hd.sp
  have xmi:x.mi=p.mi:=by unfold x allocationInput;exact hd.module
  have xo:x.outVector=scratch p+48:=by unfold x allocationInput;exact hd.out
  have xp:x.source=payloadPointer p:=by unfold x allocationInput;exact hd.source
  have xs:x.size=count p:=by unfold x allocationInput;exact hd.size
  have xha:x.allocator=1074896:=by unfold x allocationInput;exact ha
  have se:=scratch_end p hn
  have sb:=hn.spBound
  have ash:=allocatedMemory_spec p q hn hd.toAllocationDomain
  have af:=allocated_fields cfg s p q
  have ag:(allocated cfg s p q).globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)}:=by
    rw[allocated_globals cfg s p q hn hd hg]
    exact copyArguments_global cfg s p hg
  have endsp:scratch p+64=p.sp:=UInt32.sub_add_cancel p.sp 64
  have tail:=wp_tail cfg fuel rest (allocated cfg s p q) limits base e callers code
    WNear.Binary.StateDecodePrefix.invalid WNear.Binary.StateDecodePrefix.short WNear.Binary.StateDecodePrefix.panic []
    p.mi p.memoryIndex p.globalIndex p.dropAddress {p.global with value:=.i32 (scratch p)} (allocatedMemory p q)
    (scratch p) p.slice p.out (count p) post e0 e1 e2 e3 (by rw[el.1];omega)
    (by rw[ei,af.2.1];exact hcode.module) hcode.memoryIndex (allocated_memory cfg s p q hn hd hm) hcode.globalIndex ag hcode.dropAddress
    (by rw[ei,af.1];exact hcode.dropFunction) ash.1 (by rw[ash.2.1];exact hn.memoryWidth)
    (by rw[ash.2.1];omega) (by rw[ash.2.1];exact hn.sliceBound) (by rw[ash.2.1];exact hn.outBound)
    (by simpa only[allocatedMemory] using afterAllocation_split_le p q hn hd.toAllocationDomain) (by omega)
    ((allocated_gas cfg s p q hn hd _ (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega))).2.2)
    (by simpa only[tailAfter,tailLayout,after,outputted,dropped,outputLayout,droppedMemory,dropPayloadOut,exitAfter,finalFrame,e,endsp] using hnext)
  have xnative:StateDecodeVectorCopy.Native x:=allocation_copy_native p q hn hd.toAllocationDomain
  have code0:=payloadPrefix_allocation_code cfg s frame.inst p q a581 a236 hn hd.toAllocationDomain hqcode hcallback hsep
  have cn:StateDecodeVectorCopy.Code (paid (payloadPrefix cfg s p) op 7) n.inst x a581 a236:=by
    rw[ni]
    exact allocation_copy_code_paid _ op 7 frame.inst x a581 a236 code0
  have pfields:=payloadPrefix_fields cfg s p
  have pg:(payloadPrefix cfg s p).globals[x.globalIndex]?=some x.globalVector:=by
    rw[xg,xv]
    have h:=copyArguments_global cfg s p hg
    simpa only[copyArguments,paid_globals,op] using h
  have a16:(takePayloadOut p).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have words:=takenPayload_words p hn
  have ps:=takenPayload_spec p hn
  have nloc:=enoughPrefixFrame_locals (prefixLabels frame base.toArray.size code) p hs hn
  have low:readI32 x.memory ((scratch p).toNat+16)=x.source:=by rw[xm,xp];simpa only[a16] using words.1
  have high:readI32 x.memory ((scratch p).toNat+20)=x.size:=by rw[xm,xs];simpa only[a16,Nat.add_assoc,Nat.reduceAdd] using words.2
  have payload:=wp_copy_call cfg (fuel+50) (59*op+rest) (payloadPrefix cfg s p) limits base n callers
    (WNear.Binary.StateDecodePrefix.dropPayload++WNear.Binary.StateDecodePrefix.output)
    (scratch p) x a581 a236 p.copyAddress post xnative cn xha
    (by rw[xi,xm];exact payloadPrefix_memory cfg s p hm hn) pg (by rw[xv,xsp])
    (by rw[xmi];exact hcode.copyAddress)
    (by rw[pfields.1,ni];simpa only[exact374,WNear.Binary.StateDecodeVector.copySignature] using hcode.copyFunction)
    nloc.2.2.2.1 xo low.symm high.symm
    (by rw[xm,ps.2.1];omega) hdepth
    ((payloadPrefix_gas cfg s p _ (hc.mono (by dsimp[bodyCost,op];rw[xs];simp only[Nat.add_mul];omega))).2.2)
    (by simpa only[copyAfter,allocated,copyArguments,x,op,labels_enough,e,n,List.append_nil] using tail)
  have early:=wp_early cfg (fuel+(17*(count p).toNat+576)) ((18*(count p).toNat+724)*op+rest) s limits base frame callers code p post
    hn hcode hm hg hv h1 hs (by omega)
    (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega))
    (by simpa only[xs,payloadRest,n,List.append_assoc,
      show fuel+50+(17*(count p).toNat+526)=fuel+(17*(count p).toNat+576) by omega,
      show (18*(count p).toNat+665)*cfg.regularOpCost+(59*op+rest)=(18*(count p).toNat+724)*op+rest by dsimp[op];simp only[Nat.add_mul];omega] using payload)
  simpa only[bodyCost,bodySteps,Nat.add_assoc,Nat.reduceAdd,
    show 183*cfg.regularOpCost+((18*(count p).toNat+724)*op+rest)=(18*(count p).toNat+907)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using early
end WNear.Proofs.StateDecodePrefix
