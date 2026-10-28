import Proofs.StateDecodeBorshReadChildCall
import Proofs.StateDecodeBorshReadCopyPrepared
import Proofs.StateDecodeBorshReadControl
import Proofs.StateDecodeBorshReadSetupWP
import Proofs.StateDecodeBorshReadGas
import Proofs.StateDecodeBorshReadLocals

/-! Actual161 through its first sequential36-byte copy, including real162. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved sliceSaved wrapped tagCached firstDropped
  wrappedMemory packedValue tagValue reservedFrame finalFrame readI32 readI64 writeI32 writeI64
private theorem paid_plus(s:Store NearState)(op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with|zero=>rfl|succ b ih=>change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op;rw[ih]
def prefixCode:Expr:=WNear.Binary.StateDecodeBorshRead.setup++WNear.Binary.StateDecodeBorshRead.saveSlice++
  WNear.Binary.StateDecodeBorshRead.invokeWrapper++WNear.Binary.StateDecodeBorshRead.cacheResult++WNear.Binary.StateDecodeBorshRead.copyScratch
private theorem save_code:WNear.Binary.StateDecodeBorshRead.saveSlice=saveLengthCode++savePointerCode:=by rfl
private theorem invoke_code:WNear.Binary.StateDecodeBorshRead.invokeWrapper=pairArgumentsCode 3 3 96 8++[.call 162]:=by rfl
private theorem cache_code:WNear.Binary.StateDecodeBorshRead.cacheResult=cacheValueCode++cacheTagCode:=by rfl
private theorem copy_code:WNear.Binary.StateDecodeBorshRead.copyScratch=pairArgumentsCode 3 3 60 108++[.i32_const 36,.call 951,.drop]:=by rfl
private theorem cached_frame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    loadedTagFrame (reservedFrame frame p) (wrappedMemory p q) (scratch p)=finalFrame frame p q:=by
  simp only[loadedTagFrame,tagSnapshotFrame,StateDecodeScalar.loaded64Frame,finalFrame,packedFrame,packedValue,tagValue]

theorem wp_prefix(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (hg:s.globals[p.globalIndex]?=some p.global161)(hv:p.global161.value=.i32 p.sp161)
    (h0:frame.locals[0]?=some (.i32 p.out161))(h1:frame.locals[1]?=some (.i32 p.pointer))
    (h2:frame.locals[2]?=some (.i32 p.length))(hs:5≤frame.locals.size)(hdepth:callers.length+14<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(count p).toNat+3543)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (firstDropped cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+(17*(count p).toNat+3135)) (.next (atCode s limits base.toArray frame callers (prefixCode++code)))
      ((18*(count p).toNat+3543)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have rl:=reserved_locals frame p hs h0 h1 h2
  have fl:=final_locals frame p q hs h0 h1 h2
  have shape:=wrappedMemory_spec p q hn hd
  have tf:=tagCached_fields cfg s p q
  have copy:=wp_added_copy cfg fuel rest (tagCached cfg s p q) limits base (finalFrame frame p q) callers code
    3 3 (scratch p) (scratch p) 60 108 36 p.mi p.memoryIndex p.address951 (wrappedMemory p q) post fl.2.2.2.1 fl.2.2.2.1
    (by rw[finalFrame_inst,tf.2.1];exact hcode.child.child.prefixCode.child.module) hcode.child.child.prefixCode.child.memoryIndex
    (tagCached_memory cfg s p q hn hd hm) hcode.index951
    (by rw[finalFrame_inst,tf.1];exact hcode.function951) shape.1 (by decide) (by decide)
    (by rw[shape.2.1];exact hn.width) (first_copy_bounds p q hn hd).2 (first_copy_bounds p q hn hd).1 (by omega)
    (tagCached_credits cfg s p q hn hd _ (hc.mono (by simp only[Nat.add_mul];omega)))
    (by simpa only[copyDropAfter,firstDropped,firstCopied,firstCopyArguments,op] using hnext)
  let afterCache:=WNear.Binary.StateDecodeBorshRead.copyScratch++code
  have cache:=wp_cache cfg (fuel+632) (673*op+rest) (wrapped cfg s p q) limits base.toArray (reservedFrame frame p) callers afterCache
    (scratch p) p.mi p.memoryIndex (wrappedMemory p q) post rl.2.2.2.1
    (by rw[reservedFrame_inst,(wrapped_fields cfg s p q).2.1];exact hcode.child.child.prefixCode.child.module)
    hcode.child.child.prefixCode.child.memoryIndex (wrapped_memory cfg s p q hn hd hm)
    (by rw[shape.2.1];have n:=scratch_numbers p hn;omega)
    (wrapped_credits cfg s p q hn hd _ (hc.mono (by simp only[Nat.add_mul];omega)))
    (by rw[cached_frame];simpa only[tagCached,packedCached,paid_plus,Nat.reduceAdd,copy_code,afterCache,op,Nat.reduceMul,show UInt32.ofNat 36=(36:UInt32) by rfl] using copy)
  let afterChild:=WNear.Binary.StateDecodeBorshRead.cacheResult++afterCache
  have child:=wp_child_call cfg (fuel+638) (679*op+rest) s limits base (reservedFrame frame p) callers afterChild p q a581 a236 post
    hn hd (by simpa only[reservedFrame_inst] using hcode) ha hm hg rl.2.2.2.1 hdepth
    (sliceSaved_credits cfg s p _ (hc.mono (by simp only[Nat.add_mul];omega)))
    (by simpa only[cache_code,afterChild,op,Nat.add_assoc,Nat.reduceAdd,
      show 6*cfg.regularOpCost+(673*op+rest)=679*op+rest by dsimp[op];omega] using cache)
  have setup:=wp_setup cfg (fuel+(17*(count p).toNat+3124)) ((18*(count p).toNat+3532)*op+rest) s limits base frame callers
    (WNear.Binary.StateDecodeBorshRead.invokeWrapper++afterChild) p post h1 h2 (by omega)
    hcode.child.child.prefixCode.child.module hcode.child.child.prefixCode.child.memoryIndex hm
    hcode.child.child.prefixCode.child.globalIndex hg hv hn.wf (by have n:=scratch_numbers p hn;omega)
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[invoke_code,List.append_assoc,List.singleton_append,op,Nat.add_assoc,Nat.reduceAdd,
      show 638+(17*(count p).toNat+2486)=17*(count p).toNat+3124 by omega,
      show (18*(count p).toNat+2853)*cfg.regularOpCost+(679*op+rest)=(18*(count p).toNat+3532)*op+rest by dsimp[op];simp only[Nat.add_mul];omega] using child)
  simpa only[prefixCode,save_code,afterChild,afterCache,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 11*cfg.regularOpCost+((18*(count p).toNat+3532)*op+rest)=(18*(count p).toNat+3543)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using setup
end WNear.Proofs.StateDecodeBorshRead
