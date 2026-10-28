import Proofs.StateDecodeBorshReadCopyPrepared
import Proofs.StateDecodeBorshReadResources
import Proofs.StateDecodeBorshReadGas
import Proofs.StateDecodeBorshReadLocals
import Proofs.InterfaceStack
import NearVM.MeteredSelectionRules

/-! Actual161 final40-byte copy, zero tag, br1 and144-byte stack restore. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode exhausted resultCopyArguments resultCopied resultDropped tagged branched after
attribute [local irreducible] acceptedMemory resultMemory finalMemory readI32 readI64 writeI32 writeI64

def acceptedReadFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)(height:Nat)(code:Expr):CallFrame:=
  emptyBlockFrame (emptyBlockFrame (finalFrame frame p q) height (WNear.Binary.StateDecodeBorshRead.restore++code))
    height WNear.Binary.StateDecodeBorshRead.rejected
private theorem tail_code:WNear.Binary.StateDecodeBorshRead.copyResult++WNear.Binary.StateDecodeBorshRead.tagSuccess++[.br 1]=
    pairArgumentsCode 0 3 8 16++[.i32_const 40,.call 951,.drop]++[.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0},.br 1]:=by kernel_rfl
private theorem restore_code:WNear.Binary.StateDecodeBorshRead.restore=[.local_get 3,.i32_const 144,.i32_binop .add,.global_set 0]:=by kernel_rfl

theorem wp_tail(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)(post:Post)
    (hn:Native p)(hd:AcceptedDomain p q)
    (hm:s.modules[frame.inst]?=some p.mi)(hi:p.mi.memAddrs[0]?=some p.memoryIndex)
    (hgi:p.mi.globalAddrs[0]?=some p.globalIndex)
    (hfi:p.mi.funcAddrs[951]?=some p.address951)
    (hf:s.funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (he:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global161)
    (h0:(finalFrame frame p q).locals[0]?=some (.i32 p.out161))
    (h3:(finalFrame frame p q).locals[3]?=some (.i32 (scratch p)))
    (hdepth:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+708) (.next (atCode (exhausted cfg s p q) limits base.toArray
      (acceptedReadFrame frame p q base.length code) callers
      (WNear.Binary.StateDecodeBorshRead.copyResult++WNear.Binary.StateDecodeBorshRead.tagSuccess++[.br 1])))
      (753*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have sn:=scratch_numbers p hn
  have bc:(branched cfg s p q).host.gas.Credits (4*op+rest):=
    branched_credits cfg s p q hn hd _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
  have bg:(branched cfg s p q).globals[p.globalIndex]?=some {p.global161 with value:=.i32 (scratch p)}:=by
    rw[branched_globals cfg s p q hn hd hg]
    exact reserved_global s op p hg
  have restore:=InterfaceStack.wp_restore cfg fuel rest (branched cfg s p q) limits base.toArray (finalFrame frame p q) callers code
    p.mi p.globalIndex {p.global161 with value:=.i32 (scratch p)} (scratch p) 3 144 post h3
    (by rw[finalFrame_inst,(branched_fields cfg s p q).2.1];exact hm) hgi bg bc
    (by simpa only[after,sn.2.2.2,op] using hnext)
  have branch:=wp_br_two_blocks cfg (fuel+4) (4*op+rest) (tagged cfg s p q) limits base.toArray (finalFrame frame p q) callers
    (WNear.Binary.StateDecodeBorshRead.restore++code) WNear.Binary.StateDecodeBorshRead.rejected [] post
    ((tagged_credits cfg s p q hn hd (5*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];omega))
    (by simpa only[branched,restore_code,op] using restore)
  let f:=acceptedReadFrame frame p q base.length code
  have fInst:f.inst=frame.inst:=by simp only[f,acceptedReadFrame,emptyBlockFrame,finalFrame_inst]
  have f0:f.locals[0]?=some (.i32 p.out161):=by simpa only[f,acceptedReadFrame,emptyBlockFrame] using h0
  have f3:f.locals[3]?=some (.i32 (scratch p)):=by simpa only[f,acceptedReadFrame,emptyBlockFrame] using h3
  have shape:=resultMemory_spec p q hn hd
  have tag:=wp_tag_success cfg (fuel+5) (5*op+rest) (resultDropped cfg s p q) limits base.toArray f callers [.br 1] p.out161
    p.mi p.memoryIndex (resultMemory p q) post f0
    (by rw[fInst,(resultDropped_fields cfg s p q).2.1];exact hm) hi (resultDropped_memory cfg s p q hn hd he)
    (by rw[shape.2.1];have b:=hn.outBound;omega)
    (resultDropped_credits cfg s p q hn hd _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega)))
    (by simpa only[f,acceptedReadFrame,List.size_toArray,tagged,op,List.append_nil,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(4*op+rest)=5*cfg.regularOpCost+rest by dsimp[op];omega] using branch)
  have memory:=acceptedMemory_spec p q hn hd
  have width:(acceptedMemory p q).byteSize≤2^32:=by rw[memory.2.1];exact hn.width
  have copies:=wp_added_copy cfg (fuel+8) (8*op+rest) (exhausted cfg s p q) limits base f callers
    [.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0},.br 1] 0 3 p.out161 (scratch p) 8 16 40
    p.mi p.memoryIndex p.address951 (acceptedMemory p q) post f0 f3
    (by rw[fInst,(exhausted_fields cfg s p q).2.1];exact hm) hi (exhausted_memory cfg s p q hn hd he) hfi
    (by rw[fInst,(exhausted_fields cfg s p q).1];exact hf) memory.1 (by decide) (by decide) width
    (result_copy_bounds p q hn hd).2 (result_copy_bounds p q hn hd).1 hdepth
    (exhausted_credits cfg s p q hn hd _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega)))
    (by simpa only[resultDropped,resultCopied,resultCopyArguments,copyDropAfter,op,Nat.add_assoc,Nat.reduceAdd,
      show 3*cfg.regularOpCost+(5*op+rest)=8*op+rest by dsimp[op];omega] using tag)
  simpa only[show UInt32.ofNat 40=(40:UInt32) by rfl,f,tail_code,Nat.reduceMul,Nat.reduceAdd,Nat.add_assoc,
    show 745*cfg.regularOpCost+(8*op+rest)=753*cfg.regularOpCost+rest by dsimp[op];omega] using copies
end WNear.Proofs.StateDecodeBorshRead
