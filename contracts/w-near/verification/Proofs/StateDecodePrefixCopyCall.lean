import Proofs.StateDecodePrefixCopyArguments
import Proofs.StateDecodeVectorCopyCall

/-! Concrete316 argument construction and the actual374 typed invocation.
This capsule takes structural code resources at its paid argument state; the
complete316 theorem derives them from original installed code. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def copyAfter (cfg:WasmConfig)(s:Store NearState)(q:StateDecodeVectorCopy.Layout):=
  StateDecodeVectorCopy.callAfter cfg (paid s cfg.regularOpCost 7) q

theorem wp_copy_call (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (q:StateDecodeVectorCopy.Layout)(a581 a236 address:Nat)(post:Post)
    (hn:StateDecodeVectorCopy.Native q)
    (hcode:StateDecodeVectorCopy.Code (paid s cfg.regularOpCost 7) frame.inst q a581 a236)
    (ha:q.allocator=1074896)(hm:s.mems[q.memoryIndex]?=some q.memory)
    (hg:s.globals[q.globalIndex]?=some q.globalVector)(hv:q.globalVector.value=.i32 q.spVector)
    (hi:q.mi.funcAddrs[374]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeVector.copySignature frame.inst WNear.Binary.StateDecodeVector.copyFunction))
    (h2:frame.locals[2]?=some (.i32 scratch))
    (ho:q.outVector=scratch+48)(hp:q.source=readI32 q.memory (scratch.toNat+16))
    (hz:q.size=readI32 q.memory (scratch.toNat+20))(hb:scratch.toNat+24≤q.memory.byteSize)
    (hd:callers.length+10<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*q.size.toNat+665)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (copyAfter cfg s q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*q.size.toNat+526)) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.copyArguments++code)))
      ((18*q.size.toNat+665)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let args:=paid s op 7
  have ca:args.host.gas.Credits ((18*q.size.toNat+658)*cfg.regularOpCost+rest):=
    paid_credits s op 7 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have call:=StateDecodeVectorCopy.wp_call cfg fuel rest args limits base frame callers code q a581 a236 address post
    hn hcode ha (by rw[mems_paid];exact hm) (by rw[globals_paid];exact hg) hv hi
    (by rw[funcs_paid];exact hf) hd ca hnext
  have operands:(base++[Value.i32 q.outVector,.i32 q.source,.i32 q.size]).toArray=
      (((base.toArray.push (.i32 (scratch+48))).push (.i32 (readI32 q.memory (scratch.toNat+16)))).push (.i32 (readI32 q.memory (scratch.toNat+20)))):=by
    rw[ho,hp,hz];apply Array.toList_inj.mp;simp
  have cn:WP cfg (fuel+(17*q.size.toNat+519)) (.next (atCode args limits
      (((base.toArray.push (.i32 (scratch+48))).push (.i32 (readI32 q.memory (scratch.toNat+16)))).push (.i32 (readI32 q.memory (scratch.toNat+20))))
      frame callers (.call 374::code))) ((18*q.size.toNat+658)*op+rest) post:=by
    simpa only[operands,op] using call
  have pm:s.modules[frame.inst]?=some q.mi:=by
    have h:=hcode.vector.raw.record.allocation.search.module
    rw[modules_paid] at h
    exact h
  have arguments:=wp_copy_arguments cfg (fuel+(17*q.size.toNat+519)) ((18*q.size.toNat+658)*op+rest) s limits base.toArray frame callers
    (.call 374::code) scratch q.mi q.memoryIndex q.memory post h2 pm hcode.vector.raw.record.allocation.search.memoryIndex hm hb
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)) cn
  have ce:7*cfg.regularOpCost+((18*q.size.toNat+658)*op+rest)=(18*q.size.toNat+665)*cfg.regularOpCost+rest:=by dsimp[op];simp only[Nat.add_mul];omega
  simpa only[copy_arguments_exact,List.append_assoc,List.cons_append,List.nil_append,ce,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateDecodePrefix
