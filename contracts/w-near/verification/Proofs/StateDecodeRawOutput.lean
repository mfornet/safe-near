import Proofs.StateDecodeRawLocals
import Proofs.StateDecodeRawFrame
import Proofs.StateDecodeRawGas

/-! The real767 result snapshots, normal choice-block end and explicit output
return. Caller output aliases remain unrestricted. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode allocatedRaw cachedRaw afterRaw memory769
private theorem modules_paid (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih

def rawFinish : Expr := WNear.Binary.StateDecodeRaw.output++WNear.Binary.StateDecodeRaw.restore 3 32++[.return]

theorem wp_raw_output (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (p : Layout) (a581 a236 : Nat) (post : Post) (hn : Native p) (hcode : Code s frame.inst p a581 a236)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.globalRaw)
    (h0 : frame.locals[0]?=some (.i32 p.outRaw)) (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hs : 6≤frame.locals.size) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hc : s.host.gas.Credits (573*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (afterRaw cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+21) (.next (atCode (allocatedRaw cfg s p) limits base.toArray
      (emptyBlockFrame frame base.toArray.size rawFinish) (caller::callers) WNear.Binary.StateDecodeRaw.rawCache))
      (20*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=cacheFrame frame (memory769 p) (scratch p)
  have h0f:f.locals[0]?=some (.i32 p.outRaw):=by simp[f,cacheFrame,AllocateVector.loadedFrame,h0]
  have h3f:f.locals[3]?=some (.i32 (scratch p)):=by simp[f,cacheFrame,AllocateVector.loadedFrame,h3]
  have h2f:f.locals[2]?=some (.i32 (cachedPointer p)):=by
    rw[cachedPointer_eq p hn]
    simp[f,cacheFrame,AllocateVector.loadedFrame,show 2<frame.locals.size by omega]
  have h5f:f.locals[5]?=some (.i32 (cachedLength p)):=by
    simp[f,cacheFrame,cachedLength,AllocateVector.loadedFrame,show 5<frame.locals.size by omega]
  have fields:=allocatedRaw_fields cfg s p
  have cm : (cachedRaw cfg s p).modules[f.inst]?=some p.mi:=by
    rw[cachedRaw,modules_paid,fields.2.1];exact hcode.record.allocation.search.module
  have am : (allocatedRaw cfg s p).modules[frame.inst]?=some p.mi:=by
    rw[fields.2.1];exact hcode.record.allocation.search.module
  have shape:=memory769_spec p hn
  have ptr : cachedPointer p≠0 := by
    rw[(cached_words p hn).1]
    exact (allocated_spec p hn).2.2.2
  have finish:=wp_finish cfg fuel rest (cachedRaw cfg s p) limits base f caller callers [] p.mi p.memoryIndex p.globalIndex
    {p.globalRaw with value:=.i32 (scratch p)} (memory769 p) p.outRaw (cachedPointer p) (cachedLength p) (scratch p) post
    h0f h2f h5f h3f cm hcode.record.allocation.search.memoryIndex (cachedRaw_memory cfg s p hn hm)
    hcode.record.allocation.globalIndex (cachedRaw_global cfg s p hn hg) shape.1 (by rw[shape.2.1];exact hn.outBound) ptr ha hh
    ((cachedRaw_gas cfg s p _ (hc.mono (by omega))).2.2)
    (by simpa only[afterRaw] using hnext)
  have endBlock:=wp_end_label cfg (fuel+14) (14*op+rest) (cachedRaw cfg s p) limits base.toArray f (caller::callers)
    {arity:=0,height:=base.toArray.size,rest:=rawFinish,loop:=none} post
    ((cachedRaw_gas cfg s p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[rawFinish,List.append_nil] using finish)
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have sb:=hn.spBound
  have cache:=wp_cache cfg (fuel+15) (14*op+rest) (allocatedRaw cfg s p) limits base.toArray
    (emptyBlockFrame frame base.toArray.size rawFinish) (caller::callers) [] (scratch p) p.mi p.memoryIndex (memory769 p) post
    h3 am hcode.record.allocation.search.memoryIndex (allocatedRaw_memory cfg s p hn hm)
    (by rw[shape.2.1,n.1];omega)
    ((allocatedRaw_gas cfg s p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[cachedRaw,f,cacheFrame,AllocateVector.loadedFrame,emptyBlockFrame] using endBlock)
  simpa only[List.append_nil,Nat.add_assoc,Nat.reduceAdd,show 6*cfg.regularOpCost+(14*op+rest)=20*cfg.regularOpCost+rest by dsimp[op];omega] using cache
end WNear.Proofs.StateDecodeRaw
