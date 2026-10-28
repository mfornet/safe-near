import Proofs.UnwrapStateCopyEffects
import NearVM.MeteredNumericRules

/-! The real951 invocation followed by its caller's actual pointer drop.
No argument preparation or copy result is an execution premise. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode UnwrapStateCopyEntry.callAfter

def copyDropAfter(s:Store NearState)(op index:Nat)(out source:UInt32)(memory:Memory)(count:Nat):=
  paid (UnwrapStateCopyEntry.callAfter s op index out source memory count) op 1

theorem wp_copy_drop(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out source:UInt32)(count:Nat)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[951]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hw:memory.wf)(hpositive:0<count)(hcount:count<2^32)(hwidth:memory.byteSize≤2^32)
    (hr:source.toNat+count≤memory.byteSize)(hb:out.toNat+count≤memory.byteSize)
    (hd:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*count+18)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (copyDropAfter s cfg.regularOpCost index out source memory count)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*count+13)) (.next (atCode s limits
      (base++[Value.i32 out,.i32 source,.i32 (UInt32.ofNat count)]).toArray frame callers (.call 951::.drop::code)))
      ((18*count+18)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let copied:=UnwrapStateCopyEntry.callAfter s op index out source memory count
  have cc:s.host.gas.Credits ((18*count+17)*op+(op+rest)):=hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)
  have dc:copied.host.gas.Credits (op+rest):=UnwrapStateCopyEntry.callAfter_credits s op index out source memory count _ hpositive cc
  have drop:=wp_drop cfg fuel rest copied limits base.toArray frame callers code (.i32 out) post dc hnext
  have arr:(base++[Value.i32 out]).toArray=base.toArray.push (.i32 out):=by apply Array.toList_inj.mp;simp
  have call:=UnwrapStateCopyEntry.wp_call cfg (fuel+1) (op+rest) s limits base frame callers (.drop::code) out source count address mi index memory post
    hm hfi hf hi he hw hpositive hcount hwidth hr hb hd cc (by simpa only[arr] using drop)
  simpa only[Nat.add_assoc,Nat.reduceAdd,show 1+(17*count+12)=17*count+13 by omega,
    show (18*count+17)*cfg.regularOpCost+(op+rest)=(18*count+18)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using call
end WNear.Proofs.StateDecodeBorshRead
