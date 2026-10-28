import Proofs.StateDecodeBorshReadPrefix
import Proofs.StateDecodeBorshReadMiddle
import Proofs.StateDecodeBorshReadTail

/-! Complete deployed161 accepted body, real162 and all three951 calls.
The exhausted-input branch is derived from the original29-byte state header. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode firstDropped exhausted after finalFrame
private theorem accepted_parts:WNear.Binary.StateDecodeBorshRead.acceptedBody=middleCode++
    WNear.Binary.StateDecodeBorshRead.copyResult++WNear.Binary.StateDecodeBorshRead.tagSuccess++[.br 1]:=by kernel_rfl
private theorem body_parts:WNear.Binary.StateDecodeBorshRead.body=prefixCode++
    [.block .empty ([.block .empty WNear.Binary.StateDecodeBorshRead.acceptedBody]++WNear.Binary.StateDecodeBorshRead.rejected)]++
    WNear.Binary.StateDecodeBorshRead.restore:=by rw[WNear.Binary.StateDecodeBorshRead.body_segments];simp only[prefixCode,List.append_assoc]

theorem wp_body(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (hg:s.globals[p.globalIndex]?=some p.global161)(hv:p.global161.value=.i32 p.sp161)
    (h0:frame.locals[0]?=some (.i32 p.out161))(h1:frame.locals[1]?=some (.i32 p.pointer))
    (h2:frame.locals[2]?=some (.i32 p.length))(hs:5≤frame.locals.size)
    (state:WNear.State)(hw:state.WF)(hheader:StateReadHeaderBytes.At p.memory p.pointer.toNat state)(hl:p.length=29)
    (hdepth:callers.length+14<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeBorshRead.body++code))) (bodyCost p*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have fl:=final_locals frame p q hs h0 h1 h2
  let tailCode:=WNear.Binary.StateDecodeBorshRead.copyResult++WNear.Binary.StateDecodeBorshRead.tagSuccess++[.br 1]
  let af:=acceptedReadFrame frame p q base.length code
  have tail:=wp_tail cfg fuel rest s limits base frame callers code p q post hn hd
    hcode.child.child.prefixCode.child.module hcode.child.child.prefixCode.child.memoryIndex hcode.child.child.prefixCode.child.globalIndex
    hcode.index951 hcode.function951 hm hg fl.1 fl.2.2.2.1 (by omega) hc hnext
  have mid:=wp_middle cfg (fuel+708) (753*op+rest) s limits base af callers tailCode p q a581 a236 post hn hd
    (by simpa only[af,acceptedReadFrame,emptyBlockFrame,finalFrame_inst] using hcode) hm
    (by simpa only[af,acceptedReadFrame,emptyBlockFrame] using fl.2.1)
    (by simpa only[af,acceptedReadFrame,emptyBlockFrame] using fl.2.2.2.1)
    (by simpa only[af,acceptedReadFrame,emptyBlockFrame] using fl.2.2.2.2.1)
    state hw hheader hl (by omega) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega)) tail
  have inner:WP cfg (fuel+1356) (.next (atCode (firstDropped cfg s p q) limits base.toArray af callers
      WNear.Binary.StateDecodeBorshRead.acceptedBody)) (1441*op+rest) post:=by
    simpa only[accepted_parts,List.append_assoc,tailCode,Nat.add_assoc,Nat.reduceAdd,
      show 688*cfg.regularOpCost+(753*op+rest)=1441*op+rest by dsimp[op];omega] using mid
  let oframe:=emptyBlockFrame (finalFrame frame p q) base.length (WNear.Binary.StateDecodeBorshRead.restore++code)
  have blocksCredit:(firstDropped cfg s p q).host.gas.Credits (1441*op+rest):=
    firstDropped_credits cfg s p q hn hd _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
  have innerBlock:=wp_block_empty cfg (fuel+1356) (1441*op+rest) (firstDropped cfg s p q) limits base.toArray oframe callers
    WNear.Binary.StateDecodeBorshRead.acceptedBody WNear.Binary.StateDecodeBorshRead.rejected post blocksCredit
    (by simpa only[af,acceptedReadFrame,oframe,List.size_toArray] using inner)
  have outerBlock:=wp_block_empty cfg (fuel+1357) (1441*op+rest) (firstDropped cfg s p q) limits base.toArray (finalFrame frame p q) callers
    ([.block .empty WNear.Binary.StateDecodeBorshRead.acceptedBody]++WNear.Binary.StateDecodeBorshRead.rejected)
    (WNear.Binary.StateDecodeBorshRead.restore++code) post blocksCredit
    (by simpa only[oframe,List.size_toArray,List.cons_append,List.nil_append] using innerBlock)
  have pref:=wp_prefix cfg (fuel+1358) (1441*op+rest) s limits base frame callers
    (.block .empty ([.block .empty WNear.Binary.StateDecodeBorshRead.acceptedBody]++WNear.Binary.StateDecodeBorshRead.rejected)::WNear.Binary.StateDecodeBorshRead.restore++code)
    p q a581 a236 post hn hd hcode ha hm hg hv h0 h1 h2 hs hdepth
    (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[List.cons_append,Nat.add_assoc,Nat.reduceAdd] using outerBlock)
  simpa only[body_parts,bodyCost,bodySteps,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 1358+(17*(count p).toNat+3135)=17*(count p).toNat+4493 by omega,
    show (18*(count p).toNat+3543)*cfg.regularOpCost+(1441*op+rest)=(18*(count p).toNat+4984)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using pref
end WNear.Proofs.StateDecodeBorshRead
