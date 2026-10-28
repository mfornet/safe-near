import Proofs.StateDecodeVectorCopyState

/-! Complete actual374 suffix after373 returns: four arguments, actual951,
and four instructions publishing the copied length. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode UnwrapStateCopyEntry.callAfter

def suffixAfter (s:Store NearState)(op index:Nat)(memory:Memory)(out source size:UInt32):=
  finishStore (UnwrapStateCopyEntry.callAfter (paid s op 4) op index (readI32 memory out.toNat) source memory size.toNat)
    op index (ForwardCopyMemory.forward memory (readI32 memory out.toNat).toNat source.toNat size.toNat) out size

private theorem paid_modules (s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs (s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems (s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_suffix (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)
    (out source size:UInt32)(mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h1:frame.locals[1]?=some (.i32 source))(h2:frame.locals[2]?=some (.i32 size))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[951]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hw:memory.wf)(hwid:memory.byteSize≤2^32)(hb:out.toNat+12≤memory.byteSize)
    (hp:0<size.toNat)(hr:source.toNat+size.toNat≤memory.byteSize)
    (hdest:(readI32 memory out.toNat).toNat+size.toNat≤memory.byteSize)
    (hd:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*size.toNat+25)*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (suffixAfter s cfg.regularOpCost index memory out source size) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*size.toNat+20)) (.next (atCode s limits base.toArray frame callers
      (argumentsCode++(.call 951::finishCode++code)))) ((18*size.toNat+25)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let pointer:=readI32 memory out.toNat
  let args:=paid s op 4
  let copied:=UnwrapStateCopyEntry.callAfter args op index pointer source memory size.toNat
  let result:=ForwardCopyMemory.forward memory pointer.toNat source.toNat size.toNat
  have ca:args.host.gas.Credits ((18*size.toNat+17)*op+(4*op+rest)):=paid_credits s op 4 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have cc:copied.host.gas.Credits (4*op+rest):=UnwrapStateCopyEntry.callAfter_credits args op index pointer source memory size.toNat _ hp ca
  have am:args.mems[index]?=some memory:=by rw[paid_mems];exact he
  have module:args.modules[frame.inst]?=some mi:=by rw[paid_modules];exact hm
  have func:args.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function):=by rw[paid_funcs];exact hf
  have copiedMem:copied.mems[index]?=some result:=UnwrapStateCopyEffects.callAfter_memory args op index pointer source memory size.toNat am hw hwid hr hdest
  have res:=UnwrapStateCopyEffects.callAfter_resources args op index pointer source memory size.toNat
  have copiedModule:copied.modules[frame.inst]?=some mi:=by
    have eq:=congrArg (fun t:Store NearState=>t.modules) res
    change copied.modules=args.modules at eq
    rw[eq];exact module
  have shape:=ForwardCopyMemory.spec memory pointer.toNat source.toNat size.toNat hw hdest
  have outBound:out.toNat+12≤result.byteSize:=by rw[shape.2.1];exact hb
  have tailNext:WP cfg fuel (.next (atCode (finishStore copied op index result out size) limits base.toArray frame callers code)) rest post:=hn
  have tail:=wp_finish cfg fuel rest copied limits base.toArray frame callers code out size (.i32 pointer) mi index result post h0 h2 copiedModule hi copiedMem outBound cc tailNext
  have arr:(base++[Value.i32 pointer]).toArray=base.toArray.push (.i32 pointer):=by apply Array.toList_inj.mp;simp
  have callNext:WP cfg (fuel+4) (.next (atCode copied limits (base++[Value.i32 pointer]).toArray frame callers (finishCode++code))) (4*op+rest) post:=by
    simpa only[arr] using tail
  have countEq:UInt32.ofNat size.toNat=size:=UInt32.ofNat_toNat
  have small:size.toNat<2^32:=size.toNat_lt
  have call:=UnwrapStateCopyEntry.wp_call cfg (fuel+4) (4*op+rest) args limits base frame callers (finishCode++code) pointer source size.toNat address mi index memory post module hfi func hi am hw hp small hwid hr hdest hd ca callNext
  have stackEq:(base++[Value.i32 pointer,.i32 source,.i32 size]).toArray=
      ((base.toArray.push (.i32 pointer)).push (.i32 source)).push (.i32 size):=by apply Array.toList_inj.mp;simp
  have callReady:WP cfg (fuel+(17*size.toNat+16)) (.next (atCode args limits
      (((base.toArray.push (.i32 pointer)).push (.i32 source)).push (.i32 size)) frame callers (.call 951::finishCode++code)))
      ((18*size.toNat+21)*op+rest) post:=by
    simpa only[countEq,stackEq,List.cons_append,show fuel+4+(17*size.toNat+12)=fuel+(17*size.toNat+16) by omega,
      show (18*size.toNat+17)*cfg.regularOpCost+(4*op+rest)=(18*size.toNat+21)*op+rest by dsimp[op];simp only[Nat.add_mul];omega] using call
  have argsRule:=wp_arguments cfg (fuel+(17*size.toNat+16)) ((18*size.toNat+21)*op+rest) s limits base.toArray frame callers (.call 951::finishCode++code)
    out source size mi index memory post h0 h1 h2 hm hi he (by omega) (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)) callReady
  simpa only[show fuel+(17*size.toNat+16)+4=fuel+(17*size.toNat+20) by omega,
    show 4*cfg.regularOpCost+((18*size.toNat+21)*op+rest)=(18*size.toNat+25)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using argsRule
end WNear.Proofs.StateDecodeVectorCopy
