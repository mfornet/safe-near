import Proofs.StateReadOuterArguments
import Proofs.StateDecodeBorshReadCall

/-! Actual219's seven decoder arguments followed by the complete real161 call. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode StateDecodeBorshRead.callAfter readI32
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_decode_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (p:StateDecodeBorshRead.Layout)(q:StateDecodeVectorCopy.Layout)(a581 a236 address:Nat)(post:Post)
    (hn:StateDecodeBorshRead.Native p)(hd:StateDecodeBorshRead.AcceptedDomain p q)
    (hcode:StateDecodeBorshRead.Code s frame.inst p q a581 a236)(ha:q.allocator=1074896)
    (hout:p.out161=r+40)(hptr:p.pointer=readI32 p.memory (r.toNat+0))(hlen:p.length=readI32 p.memory (r.toNat+4))
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global161)(hv:p.global161.value=.i32 p.sp161)
    (h1:frame.locals[1]?=some (.i32 r))(hb:r.toNat+8≤p.memory.byteSize)
    (state:WNear.State)(hw:state.WF)(hheader:StateReadHeaderBytes.At p.memory p.pointer.toNat state)(hl:p.length=29)
    (hi:p.mi.funcAddrs[161]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeBorshRead.signature frame.inst WNear.Binary.StateDecodeBorshRead.function))
    (hdepth:callers.length+15<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(StateDecodeBorshRead.count p).toNat+5003)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (StateDecodeBorshRead.callAfter cfg (paid s cfg.regularOpCost 7) p q)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*(StateDecodeBorshRead.count p).toNat+4502)) (.next (atCode s limits base.toArray frame callers
      (decodeArgumentsCode++[.call 161]++code)))
      ((18*(StateDecodeBorshRead.count p).toNat+5003)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=paid s op 7
  have co:StateDecodeBorshRead.Code active frame.inst p q a581 a236:=hcode.transport s active frame.inst p q a581 a236
    (paid_funcs s op 7) (paid_modules s op 7) (paid_tables s op 7)
  have cc:active.host.gas.Credits ((18*(StateDecodeBorshRead.count p).toNat+4996)*op+rest):=
    paid_credits s op 7 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have call:=StateDecodeBorshRead.wp_call cfg fuel rest active limits base frame callers code p q a581 a236 address post hn hd co ha
    (by rw[paid_mems];exact hm) (by rw[paid_globals];exact hg) hv state hw hheader hl hi (by rw[paid_funcs];exact hf) hdepth cc hnext
  have arr:(base++[Value.i32 p.out161,.i32 p.pointer,.i32 p.length]).toArray=
      ((base.toArray.push (.i32 (r+40))).push (.i32 (readI32 p.memory (r.toNat+0)))).push (.i32 (readI32 p.memory (r.toNat+4))):=by
    rw[hout,hptr,hlen];apply Array.toList_inj.mp;simp
  have next:WP cfg (fuel+(17*(StateDecodeBorshRead.count p).toNat+4495)) (.next (atCode active limits
      (((base.toArray.push (.i32 (r+40))).push (.i32 (readI32 p.memory (r.toNat+0)))).push (.i32 (readI32 p.memory (r.toNat+4))))
      frame callers (.call 161::code))) ((18*(StateDecodeBorshRead.count p).toNat+4996)*op+rest) post:=by
    rw[arr] at call
    exact call
  have module:s.modules[frame.inst]?=some p.mi:=hcode.child.child.prefixCode.child.module
  have index:p.mi.memAddrs[0]?=some p.memoryIndex:=hcode.child.child.prefixCode.child.memoryIndex
  have args:=wp_decode_arguments cfg (fuel+(17*(StateDecodeBorshRead.count p).toNat+4495))
    ((18*(StateDecodeBorshRead.count p).toNat+4996)*op+rest) s limits base.toArray frame callers (.call 161::code) r 0 p.mi p.memoryIndex p.memory post
    h1 module index hm hb (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)) next
  have ce:7*cfg.regularOpCost+((18*(StateDecodeBorshRead.count p).toNat+4996)*op+rest)=
      (18*(StateDecodeBorshRead.count p).toNat+5003)*cfg.regularOpCost+rest:=by dsimp[op];simp only[Nat.add_mul];omega
  rw[ce] at args
  simpa only[List.singleton_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.StateReadOuter
