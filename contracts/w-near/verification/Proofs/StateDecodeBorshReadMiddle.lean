import Proofs.StateDecodeBorshReadCopyPrepared
import Proofs.StateDecodeBorshReadPacked
import Proofs.StateDecodeBorshReadExhausted
import Proofs.StateDecodeBorshReadCode
import Proofs.StateDecodeBorshReadGas
import Proofs.StateDecodeBorshReadResources
import Proofs.StateDecodeBorshReadHeader

/-! Actual161 accepted guard, upper-word store, overlapping36-byte copy and
CURRENT descriptor exhaustion guard. Every resource follows original inputs. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode firstDropped guarded upperSaved acceptedCopyArguments acceptedCopied acceptedDropped exhausted
  scratchMemory upperMemory acceptedMemory packedValue tagValue readI32 readI64 writeI32 writeI64

def upperCode:Expr:=[.local_get 3,.local_get 4,.i64_const 32,.i64_binop .shr_u,.store .i64 (some 32) {align:=2,offset:=16}]
def middleCode:Expr:=guardCode++upperCode++orCopyArgumentsCode++[.call 951,.drop]++
  [.block .empty (WNear.Binary.StateDecodeBorshRead.exhaustionGuard++WNear.Binary.StateDecodeBorshRead.trailingBytesRejected)]
private theorem exhausted_code:WNear.Binary.StateDecodeBorshRead.exhaustionGuard=
    [.local_get 3,.load .i32 none {align:=2,offset:=12},.i32_eqz,.br_if 0]:=by rfl

theorem wp_middle(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)
    (h1:frame.locals[1]?=some (.i32 (tagValue p q)))(h3:frame.locals[3]?=some (.i32 (scratch p)))
    (h4:frame.locals[4]?=some (.i64 (packedValue p q)))
    (state:WNear.State)(hw:state.WF)(hheader:StateReadHeaderBytes.At p.memory p.pointer.toNat state)(hl:p.length=29)
    (hdepth:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4231)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (exhausted cfg s p q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+648) (.next (atCode (firstDropped cfg s p q) limits base.toArray frame callers (middleCode++code)))
      (688*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have n:=scratch_numbers p hn
  have ashape:=acceptedMemory_spec p q hn hd
  have ushape:=upperMemory_spec p q hn hd
  have sshape:=scratchMemory_spec p q hn hd
  have af:=acceptedDropped_fields cfg s p q
  have uf:=upperSaved_fields cfg s p q
  have gf:=guarded_fields cfg s p q
  have endCall:=wp_exhausted cfg fuel rest (acceptedDropped cfg s p q) limits base.toArray frame callers code
    WNear.Binary.StateDecodeBorshRead.trailingBytesRejected (scratch p) p.mi p.memoryIndex (acceptedMemory p q) post h3
    (by rw[af.2.1];exact hcode.child.child.prefixCode.child.module) hcode.child.child.prefixCode.child.memoryIndex
    (acceptedDropped_memory cfg s p q hn hd hm) (by rw[ashape.2.1];omega)
    (acceptedMemory_exhausted_header p q hn hd state hw hheader hl)
    (acceptedDropped_credits cfg s p q hn hd _ (hc.mono (by simp only[Nat.add_mul];omega)))
    (by simpa only[exhausted,op] using hnext)
  have orCall:=wp_or_copy cfg (fuel+5) (4*op+rest) (upperSaved cfg s p q) limits base frame callers
    (.block .empty (WNear.Binary.StateDecodeBorshRead.exhaustionGuard++WNear.Binary.StateDecodeBorshRead.trailingBytesRejected)::code)
    (scratch p) p.mi p.memoryIndex p.address951 (upperMemory p q) post h3
    (by rw[uf.2.1];exact hcode.child.child.prefixCode.child.module) hcode.child.child.prefixCode.child.memoryIndex
    (upperSaved_memory cfg s p q hn hd hm) hcode.index951 (by rw[uf.1];exact hcode.function951)
    ushape.1 (by rw[ushape.2.1];exact hn.width) (accepted_copy_bounds p q hn hd).2 (accepted_copy_bounds p q hn hd).1 hdepth
    (upperSaved_credits cfg s p q hn hd _ (hc.mono (by simp only[op,Nat.add_mul];omega)))
    (by simpa only[copyDropAfter,acceptedDropped,acceptedCopied,acceptedCopyArguments,op,exhausted_code] using endCall)
  have packed:=wp_packed_store cfg (fuel+639) (679*op+rest) (guarded cfg s p q) limits base.toArray frame callers
    (orCopyArgumentsCode++[.call 951,.drop]++[.block .empty (WNear.Binary.StateDecodeBorshRead.exhaustionGuard++WNear.Binary.StateDecodeBorshRead.trailingBytesRejected)]++code)
    (scratch p) (packedValue p q) p.mi p.memoryIndex (scratchMemory p q) post h3 h4
    (by rw[gf.2.1];exact hcode.child.child.prefixCode.child.module) hcode.child.child.prefixCode.child.memoryIndex
    (guarded_memory cfg s p q hn hd hm) (by rw[sshape.2.1];omega)
    (guarded_credits cfg s p q hn hd _ (hc.mono (by simp only[op,Nat.add_mul];omega)))
    (by simpa only[upperStore,upperSaved,op,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 675*cfg.regularOpCost+(4*op+rest)=679*op+rest by simp only[op];omega] using orCall)
  have check:=wp_accepted_guard cfg (fuel+644) (684*op+rest) (firstDropped cfg s p q) limits base.toArray frame callers
    (upperCode++orCopyArgumentsCode++[.call 951,.drop]++[.block .empty (WNear.Binary.StateDecodeBorshRead.exhaustionGuard++WNear.Binary.StateDecodeBorshRead.trailingBytesRejected)]++code)
    (tagValue p q) post h1 (by rw[tagValue_zero p q hn hd];decide)
    (firstDropped_credits cfg s p q hn hd _ (hc.mono (by simp only[op,Nat.add_mul];omega)))
    (by simpa only[guarded,op,upperCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 5*cfg.regularOpCost+(679*op+rest)=684*op+rest by simp only[op];omega] using packed)
  simpa only[middleCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 4*cfg.regularOpCost+(684*op+rest)=688*cfg.regularOpCost+rest by simp only[op];omega] using check
end WNear.Proofs.StateDecodeBorshRead
