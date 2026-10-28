import Proofs.StateDecodeBorshMiddleWP
import Proofs.StateDecodeBorshNarrowTail
import Proofs.StateDecodeBorshPrefixCall
import Proofs.StateDecodeBorshExit

/-! The complete accepted deployed425 body. It executes all actual315/372/371
calls and four block entries, then returns to the original code continuation.
Every phase resource/domain is derived from the original conditions. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved prefixDecoded prefixCached prefixGuarded after
  prefixFrame savedPrefixFrame wideFrame finalFrame prefixMemory savedPrefixMemory savedWideMemory narrowMemory
  readI32 readI64 writeI32 writeI64

def threeFrame(frame:CallFrame)(height:Nat)(code:Expr):=
  emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame height (WNear.Binary.StateDecodeBorsh.restore++code))
    height WNear.Binary.StateDecodeBorsh.wideRejected) height WNear.Binary.StateDecodeBorsh.prefixRejected
private theorem prefix_three(frame:CallFrame)(height:Nat)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    prefixFrame (threeFrame frame height code) p q=threeFrame (prefixFrame frame p q) height code:=by
  simp only[prefixFrame,reservedFrame,threeFrame,emptyBlockFrame]
private theorem wide_three(frame:CallFrame)(height:Nat)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    wideFrame (threeFrame frame height code) p q=narrowTailFrame frame p q height code:=by
  simp only[wideFrame,savedPrefixFrame,prefixFrame,reservedFrame,threeFrame,narrowTailFrame,emptyBlockFrame]
private theorem accepted_eq:
    WNear.Binary.StateDecodeBorsh.accepted=WNear.Binary.StateDecodeBorsh.prefixGuard++middleCode++
      ([.block .empty WNear.Binary.StateDecodeBorsh.acceptedNarrow]++WNear.Binary.StateDecodeBorsh.narrowRejected):=by
  simp only[WNear.Binary.StateDecodeBorsh.accepted,middleCode,List.append_assoc]

theorem wp_body(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)(hcallback:p.sp.toNat≤1057464+16)
    (hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global425)(hv:p.global425.value=.i32 p.sp425)
    (h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:8≤frame.locals.size)
    (hdepth:callers.length+12<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeBorsh.body++code)))
      (bodyCost p*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=threeFrame frame base.toArray.size code
  let cTail:Expr:=[.block .empty WNear.Binary.StateDecodeBorsh.acceptedNarrow]++WNear.Binary.StateDecodeBorsh.narrowRejected
  have tail:=wp_narrow_tail cfg fuel rest s limits base frame callers code p q a581 a236 post hn hd hcode hm hg h0 h1 hs hc hnext
  have mid:=wp_middle cfg (fuel+58) rest s limits base f callers cTail p q a581 a236 post hn hd
    (by simpa only[f,threeFrame,emptyBlockFrame] using hcode) hm hg h0 h1 hs (by omega) hc
    (by rw[wide_three];exact tail)
  have pf:Code s (prefixFrame f p q).inst p q a581 a236:=by simpa only[prefixFrame_inst,f,threeFrame,emptyBlockFrame] using hcode
  have shape:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  have memoryEq:StateDecodePrefixWrapper.finalMemory p.toPrefixWrapper q=prefixMemory p q:=by unfold prefixMemory;rfl
  rw[memoryEq] at shape
  have n:=scratch_numbers p hn
  have pl:=prefix_locals f p q hs h0 h1
  have c450:(prefixCached cfg s p q).host.gas.Credits (450*op+rest):=
    prefixCached_credits cfg s p q hn hd _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
  have guard:=wp_guard cfg (fuel+379) (445*op+rest) (prefixCached cfg s p q) limits base.toArray (prefixFrame f p q) callers
    (middleCode++cTail) 0 (scratch p) p.mi p.memoryIndex (prefixMemory p q) post pl.2.2.1
    (by rw[prefixFrame_inst];change (prefixCached cfg s p q).modules[frame.inst]?=some p.mi;rw[(prefixCached_fields cfg s p q).2.1];exact hcode.prefixCode.child.module)
    hcode.prefixCode.child.memoryIndex (prefixCached_memory cfg s p q hn hd hm) (by rw[shape.2.1];omega)
    (by rw[prefixMemory_tag p q hn hd];decide) (c450.mono (by dsimp[op];omega))
    (by simpa only[prefixGuarded,op,Nat.add_assoc,Nat.reduceAdd] using mid)
  have accepted:WP cfg (fuel+384) (.next (atCode (prefixCached cfg s p q) limits base.toArray
      (threeFrame (prefixFrame frame p q) base.toArray.size code) callers WNear.Binary.StateDecodeBorsh.accepted)) (450*op+rest) post:=by
    simpa only[accepted_eq,prefix_guard_exact,prefix_three,f,cTail,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 5*cfg.regularOpCost+(445*op+rest)=450*op+rest by dsimp[op];omega] using guard
  let outer:=emptyBlockFrame (prefixFrame frame p q) base.toArray.size (WNear.Binary.StateDecodeBorsh.restore++code)
  let middle:=emptyBlockFrame outer base.toArray.size WNear.Binary.StateDecodeBorsh.wideRejected
  have innerBlock:=wp_block_empty cfg (fuel+384) (450*op+rest) (prefixCached cfg s p q) limits base.toArray middle callers
    WNear.Binary.StateDecodeBorsh.accepted WNear.Binary.StateDecodeBorsh.prefixRejected post c450 accepted
  have middleBlock:=wp_block_empty cfg (fuel+385) (450*op+rest) (prefixCached cfg s p q) limits base.toArray outer callers
    ([.block .empty WNear.Binary.StateDecodeBorsh.accepted]++WNear.Binary.StateDecodeBorsh.prefixRejected)
    WNear.Binary.StateDecodeBorsh.wideRejected post c450 (by simpa only[middle,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using innerBlock)
  have outerBlock:=wp_block_empty cfg (fuel+386) (450*op+rest) (prefixCached cfg s p q) limits base.toArray (prefixFrame frame p q) callers
    ([.block .empty ([.block .empty WNear.Binary.StateDecodeBorsh.accepted]++WNear.Binary.StateDecodeBorsh.prefixRejected)]++WNear.Binary.StateDecodeBorsh.wideRejected)
    (WNear.Binary.StateDecodeBorsh.restore++code) post c450 (by simpa only[outer,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using middleBlock)
  let restCode:Expr:=[.block .empty ([.block .empty ([.block .empty WNear.Binary.StateDecodeBorsh.accepted]++WNear.Binary.StateDecodeBorsh.prefixRejected)]++WNear.Binary.StateDecodeBorsh.wideRejected)]++WNear.Binary.StateDecodeBorsh.restore++code
  have rl:=reserved_locals frame p hs h0 h1
  have cache:=wp_cache_prefix cfg (fuel+387) (450*op+rest) (prefixDecoded cfg s p q) limits base.toArray (reservedFrame frame p) callers restCode
    (scratch p) p.mi p.memoryIndex (prefixMemory p q) post rl.2.2.1
    (by rw[reservedFrame_inst,(prefixDecoded_fields cfg s p q).2.1];exact hcode.prefixCode.child.module)
    hcode.prefixCode.child.memoryIndex (prefixDecoded_memory cfg s p q hn hd hm) (by rw[shape.2.1];omega)
    ((prefixDecoded_credits cfg s p q hn hd (453*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];omega))
    (by rw[cachePrefixFrame_eq];simpa only[prefixCached,restCode,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,op] using outerBlock)
  have rc:Code (reserved s op p) (reservedFrame frame p).inst p q a581 a236:=by
    rw[reservedFrame_inst];exact hcode.reserved s op frame.inst p q a581 a236
  have rg:(reserved s op p).globals[p.globalIndex]?=some p.wrapperGlobal:=by
    rw[hn.childGlobal];exact reserved_global s op p hg
  have call:=PrefixCall.wp_call cfg (fuel+390) (453*op+rest) (reserved s op p) limits base (reservedFrame frame p) callers
    (WNear.Binary.StateDecodeBorsh.cachePrefix++restCode) p q a581 a236 post hn hd rc ha hcallback hsep
    (reserved_memory cfg s p hm) rg rl.2.1 rl.2.2.1 hdepth
    ((reserved_credits cfg s p ((18*(count p).toNat+1429)*op+rest)
      (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[PrefixCall.after,prefixDecoded,prefixArguments,op,Nat.add_assoc,Nat.reduceAdd,
      show 3*cfg.regularOpCost+(450*op+rest)=453*op+rest by dsimp[op];omega] using cache)
  have setup:=wp_setup cfg (fuel+(17*(count p).toNat+1165)) ((18*(count p).toNat+1429)*op+rest) s limits base.toArray frame callers
    (WNear.Binary.StateDecodeBorsh.prefixArguments++[.call 315]++WNear.Binary.StateDecodeBorsh.cachePrefix++restCode)
    p.mi p.globalIndex p.global425 p.sp425 post hcode.prefixCode.child.module hcode.prefixCode.child.globalIndex hg hv
    (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[setupStore,setupResultFrame,reserved,reservedFrame,scratch,op,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 390+(17*(count p).toNat+775)=17*(count p).toNat+1165 by omega,
      show (18*(count p).toNat+976)*cfg.regularOpCost+(453*cfg.regularOpCost+rest)=(18*(count p).toNat+1429)*cfg.regularOpCost+rest by simp only[Nat.add_mul];omega] using call)
  simpa only[WNear.Binary.StateDecodeBorsh.body_segments,WNear.Binary.StateDecodeBorsh.structuredBody,restCode,bodySteps,bodyCost,List.append_assoc,
    Nat.add_assoc,Nat.reduceAdd,show 5*cfg.regularOpCost+((18*(count p).toNat+1429)*op+rest)=(18*(count p).toNat+1434)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using setup
end WNear.Proofs.StateDecodeBorsh
