import Proofs.StateDecodeScalarOutputTail
import Proofs.StateDecodeScalarDropCall

/-! Full accepted scalar suffix, using actual slice-drop invocation and cached
word snapshots before the caller-visible writes. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode accepted cached dropped dropCached readWords wordMemory droppedMemory
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_tail (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native wide p) (hcode : Code wide s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.slice))
    (hs : (if wide then 7 else 6)≤frame.locals.size) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost wide*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after wide cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+(if wide then 59 else 51)) (.next (atCode (accepted wide cfg s p) limits base.toArray
      (acceptedFrame wide frame p base.length code) (caller::callers) (successTail wide)))
      ((if wide then 67 else 59)*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let outer:=emptyBlockFrame (guardedFrame frame p) base.length (WNear.Binary.StateDecodeScalar.invalid wide++code)
  let start:=acceptedFrame wide frame p base.length code
  let cf:=cachedFrame wide start p
  let df:=dropCachedFrame wide cf p
  let outFrame:=dropCachedFrame wide (cachedFrame wide outer p) p
  have ls:=dropCached_locals wide frame p hs h0 h1
  have cs:=cached_locals wide frame p hs h0 h1
  have gs:=guarded_locals wide frame p hs h0 h1
  have oc : Code wide s outFrame.inst p := by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,dropCachedFrame_inst,cachedFrame_inst,emptyBlockFrame,guardedFrame] using hcode
  have output:=wp_output_tail wide cfg fuel rest s limits base outFrame caller callers p post hn oc hm hg
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame] using ls.1)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame] using ls.2.1)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame] using ls.2.2.1)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame] using ls.2.2.2.2.1)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame] using ls.2.2.2.2.2.1)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame] using ls.2.2.2.2.2.2.1)
    (by
      cases wide <;> simp only [outFrame,outer,emptyBlockFrame,dropCachedFrame,cachedFrame,Array.size_set!,ite_true,Bool.false_eq_true,ite_false]
      all_goals rw [gs.2.2.2.2]
      all_goals (simp only [ite_true,Bool.false_eq_true,ite_false] at hs;omega))
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,dropCachedFrame,cachedFrame,emptyBlockFrame,guardedFrame] using ha)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,outFrame,outer,dropCachedFrame,cachedFrame,emptyBlockFrame,guardedFrame] using hh) hc hnext
  have dc:=Code.dropped wide cfg s frame.inst p hcode
  have dl : (dropped wide cfg s p).modules[cf.inst]?=some p.mi := by
    cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,cf,start,acceptedFrame,cachedFrame,emptyBlockFrame,guardedFrame] using dc.module
  have shape:=droppedMemory_spec wide p hn
  have se:=scratch_end wide p hn
  have dropCache:=wp_drop_cache cfg (fuel+(if wide then 24 else 19)) ((if wide then 23 else 18)*op+rest)
    (dropped wide cfg s p) limits base.toArray cf (caller::callers)
    (WNear.Binary.StateDecodeScalar.outputValues wide++WNear.Binary.StateDecodeScalar.updateSlice wide) wide (scratch p) p.mi p.memoryIndex (droppedMemory wide p) post
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,cf,start,acceptedFrame,cachedFrame,emptyBlockFrame] using cs.2.2.1) dl hcode.memoryIndex
    (dropped_memory wide cfg s p hm) (by rw [shape.2.1];have sb:=hn.spBound;omega)
    (dropped_credits wide cfg s p _ (hc.mono (by cases wide <;> simp only [bodyCost,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega)))
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,dropCached,dropCacheFrame_eq,df,cf,start,acceptedFrame,outFrame,outer,cachedFrame,dropCachedFrame,emptyBlockFrame] using output)
  have ccode:=Code.readWords wide cfg s frame.inst p hcode
  have cm : (cached wide cfg s p).modules[cf.inst]?=some p.mi := by
    simp only [cached,accepted,modules_paid]
    cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,cf,start,acceptedFrame,cachedFrame,emptyBlockFrame,guardedFrame] using ccode.module
  have cfns : (cached wide cfg s p).funcs[p.addressDrop]?=some (.wasm WNear.Binary.StateDecodeSlices.signature cf.inst (WNear.Binary.StateDecodeSlices.function true)) := by
    simp only [cached,accepted,funcs_paid]
    cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,cf,start,acceptedFrame,cachedFrame,emptyBlockFrame,guardedFrame] using ccode.dropFunction
  have cmem : (cached wide cfg s p).mems[p.memoryIndex]?=some (wordMemory wide p) := by
    rw[cached,accepted,mems_paid,mems_paid];exact readWords_memory wide cfg s p hm
  have wshape:=wordMemory_spec wide p hn
  have descr:=word_descriptor wide p hn
  have db:=scratch_spans wide p hn
  have drop:=wp_drop_call cfg ((fuel+(if wide then 24 else 19))+3) (3*op+((if wide then 23 else 18)*op+rest))
    (cached wide cfg s p) limits base cf (caller::callers)
    (WNear.Binary.StateDecodeScalar.dropCache wide++WNear.Binary.StateDecodeScalar.outputValues wide++WNear.Binary.StateDecodeScalar.updateSlice wide)
    wide (scratch p) p.slice p.pointer p.length p.mi p.memoryIndex p.addressDrop (wordMemory wide p) post
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,cf,start,acceptedFrame,cachedFrame,emptyBlockFrame] using cs.2.1)
    (by cases wide <;> simpa only [ite_true,Bool.false_eq_true,ite_false,reservedFrame,cf,start,acceptedFrame,cachedFrame,emptyBlockFrame] using cs.2.2.1)
    cm hcode.memoryIndex cmem hcode.dropAddress cfns wshape.1
    (by rw[wshape.2.1];exact hn.sliceBound)
    (by change (dropOut wide p).toNat+8≤_;rw[wshape.2.1];exact Nat.le_trans db.2.2 hn.spBound)
    descr.1 descr.2 (by cases wide <;> exact hn.lengthAccepted)
    (by simpa only[List.length_cons] using hd)
    (cached_credits wide cfg s p _ (hc.mono (by cases wide <;> simp only [bodyCost,dropArgumentCount,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega)))
    (by simpa only [dropOut,width,dropAfter,dropped,dropArguments,dropArgumentCount,List.append_assoc,op] using dropCache)
  have am : (accepted wide cfg s p).modules[start.inst]?=some p.mi := by
    rw[accepted,modules_paid]
    simpa only[start,acceptedFrame,emptyBlockFrame,guardedFrame,reservedFrame] using ccode.module
  have amem : (accepted wide cfg s p).mems[p.memoryIndex]?=some (wordMemory wide p) := by
    rw[accepted,mems_paid];exact readWords_memory wide cfg s p hm
  have cache:=wp_cache cfg (((fuel+(if wide then 24 else 19))+3)+dropArgumentCount wide+17)
    ((dropArgumentCount wide+26)*op+(3*op+((if wide then 23 else 18)*op+rest))) (accepted wide cfg s p)
    limits base.toArray start (caller::callers)
    (WNear.Binary.StateDecodeScalar.dropArguments wide++WNear.Binary.StateDecodeScalar.dropCache wide++WNear.Binary.StateDecodeScalar.outputValues wide++WNear.Binary.StateDecodeScalar.updateSlice wide)
    wide (scratch p) p.mi p.memoryIndex (wordMemory wide p) post
    (by simpa only[start,acceptedFrame,emptyBlockFrame] using gs.2.2.1) am hcode.memoryIndex amem
    (by rw[wshape.2.1];have sb:=hn.spBound;omega) (scratch_add wide p hn 25 (by omega))
    (accepted_credits wide cfg s p _ (hc.mono (by cases wide <;> simp only [bodyCost,cacheCost,dropArgumentCount,ite_true,Bool.false_eq_true,ite_false] <;> dsimp[op] <;> omega)))
    (by simpa only[cached,cacheCost,cacheFrame_eq,cf,List.append_assoc,op] using drop)
  cases wide <;> simpa only [successTail,cacheCost,dropArgumentCount,ite_true,Bool.false_eq_true,ite_false,
    Nat.add_assoc,Nat.reduceAdd,List.append_assoc,op,Nat.reduceMul,
    show 8*op+((7+26)*op+(3*op+(23*op+rest)))=67*op+rest by omega,
    show 3*op+((9+26)*op+(3*op+(18*op+rest)))=59*op+rest by omega] using cache
end WNear.Proofs.StateDecodeScalar
