import Proofs.StateReadOuterArguments
import Proofs.StateDecodeBorshReadCopyCall

/-! The real219 result-copy arguments,951 invocation and actual result drop. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode StateDecodeBorshRead.copyDropAfter
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_output_copy(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r out:UInt32)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))(h0:frame.locals[0]?=some (.i32 out))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[951]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hw:memory.wf)(hwidth:memory.byteSize≤2^32)(hr:((r+40)+8).toNat+40≤memory.byteSize)(hb:out.toNat+40≤memory.byteSize)
    (hd:callers.length+1<limits.maxCallDepth)(hc:s.host.gas.Credits (745*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (StateDecodeBorshRead.copyDropAfter (paid s cfg.regularOpCost 7) cfg.regularOpCost index out ((r+40)+8) memory 40)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+700) (.next (atCode s limits base.toArray frame callers (copyArgumentsCode++[.call 951,.drop]++code)))
      (745*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have call:=StateDecodeBorshRead.wp_copy_drop cfg fuel rest (paid s op 7) limits base frame callers code out ((r+40)+8) 40 mi index address memory post
    (by rw[paid_modules];exact hm) hi (by rw[paid_mems];exact he) hfi (by rw[paid_funcs];exact hf) hw (by decide) (by decide) hwidth hr hb hd
    (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) hnext
  have arr:(base++[Value.i32 out,.i32 ((r+40)+8),.i32 (UInt32.ofNat 40)]).toArray=
      ((base.toArray.push (.i32 out)).push (.i32 ((r+40)+8))).push (.i32 40):=by apply Array.toList_inj.mp;simp
  have next:WP cfg (fuel+693) (.next (atCode (paid s op 7) limits
      (((base.toArray.push (.i32 out)).push (.i32 ((r+40)+8))).push (.i32 40)) frame callers (.call 951::.drop::code)))
      (738*op+rest) post:=by simpa only[arr,Nat.reduceMul,Nat.reduceAdd,op] using call
  have args:=wp_copy_arguments cfg (fuel+693) (738*op+rest) s limits base.toArray frame callers (.call 951::.drop::code) r out post h1 h0
    (hc.mono (by dsimp[op];omega)) next
  have ce:7*cfg.regularOpCost+(738*op+rest)=745*cfg.regularOpCost+rest:=by dsimp[op];omega
  rw[ce] at args
  simpa only[List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.StateReadOuter
