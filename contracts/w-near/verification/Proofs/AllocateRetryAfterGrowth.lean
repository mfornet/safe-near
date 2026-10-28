import Proofs.AllocateRetrySecond
import Proofs.AllocateRetryRelink
import Proofs.AllocateRetryCode
import Proofs.AllocateRetryGas

/-! Actual successful growth result check, relink, and second search of581. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode grown checked oldLinked relinked retried found beforeGrow firstAttempt prefixed
  AllocateGrowth.callAfter AllocateGrowth.finalMemory AllocateFlagged.callAfter secondFrom growthLayout AllocateGrowth.delta memoryGrowCost

theorem wp_after_growth (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h4 : frame.locals[4]?=some (.i32 (words p))) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (scratch p))) (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits (582*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest))
    (hnext : WP cfg fuel (.next (atCode (found cfg s p) limits base.toArray (secondFrame frame p) callers code)) rest post) :
    WP cfg (fuel+263) (.next (atCode (grown cfg s p) limits base.toArray
      (missedFrame (emptyBlockFrame frame base.toArray.size code)) callers
      (WNear.Binary.AllocateRetry.growthCheck++WNear.Binary.AllocateRetry.relink++WNear.Binary.AllocateRetry.secondAttempt)))
      (300*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))
  let bf := emptyBlockFrame frame base.toArray.size code
  let mf := missedFrame bf
  let head := AllocateGrowth.header (growthLayout p)
  let lf := linkFrame mf head
  let memory := AllocateGrowth.finalMemory (growthLayout p)
  have cg : (grown cfg s p).host.gas.Credits (300*op+rest) := (grown_gas cfg s p).credits (hc.mono (by simp only [op];omega))
  have cc : (checked cfg s p).host.gas.Credits (295*op+rest) :=
    (checked_gas cfg s p).credits (hc.mono (by simp only [op];omega))
  have cl : (relinked cfg s p).host.gas.Credits (286*op+rest) :=
    (relinked_gas cfg s p).credits (hc.mono (by simp only [op];omega))
  have cf : (found cfg s p).host.gas.Credits rest := (found_gas cfg s p).credits hc
  let label : Label := ⟨0,base.toArray.size,code,none⟩
  have endNext : WP cfg fuel (.next (atCode (found cfg s p) limits base.toArray (secondFrame frame p) callers label.rest)) rest post := hnext
  have endLabel := wp_end_label cfg fuel rest (found cfg s p) limits base.toArray (secondFrame frame p) callers label post cf endNext
  have secondNext : WP cfg (fuel+1) (.next (atCode (secondFrom (relinked cfg s p) op p) limits base.toArray (secondFrame lf p) callers [])) rest post := by
    simpa only [secondFrom,found,retried,op,lf,mf,bf,secondFrame,linkFrame,missedFrame,emptyBlockFrame,label,Array.set!_eq_setIfInBounds,Array.setIfInBounds_setIfInBounds] using endLabel
  have fields := relinked_fields cfg s p
  have codeL := (hcode.transport s (relinked cfg s p) frame.inst p fields.1 fields.2.1 fields.2.2).second _ _ p hn
  have moduleL : Code (relinked cfg s p) lf.inst p := by simpa only [lf,linkFrame,mf,missedFrame,bf,emptyBlockFrame] using hcode.transport s _ frame.inst p fields.1 fields.2.1 fields.2.2
  have h4l : lf.locals[4]?=some (.i32 (words p)) := by simp [lf,linkFrame,mf,missedFrame,bf,emptyBlockFrame,h4]
  have h2l : lf.locals[2]?=some (.i32 1) := by simp [lf,linkFrame,mf,missedFrame,bf,emptyBlockFrame,h2]
  have h3l : lf.locals[3]?=some (.i32 (scratch p)) := by simp [lf,linkFrame,mf,missedFrame,bf,emptyBlockFrame,h3]
  have second := wp_second_attempt cfg (fuel+1) rest (relinked cfg s p) limits base lf callers [] p post hn h4l h2l h3l
    (moduleL.second _ _ p hn) (relinked_memory cfg s p hmem) moduleL.originalCode.searchIndex moduleL.originalCode.searchFunction hd cl secondNext
  have secondBridge : WP cfg (fuel+249) (.next (atCode (relinked cfg s p) limits base.toArray lf callers WNear.Binary.AllocateRetry.secondAttempt)) (286*op+rest) post := by
    simpa only [List.append_nil,Nat.add_assoc,Nat.reduceAdd] using second
  have shapes := AllocateGrowth.finalMemory_spec (growthLayout p) hn.growth
  have grow := hn.growth.grown_spec (growthLayout p)
  have memorySize : (growthLayout p).memory.byteSize=p.memory.byteSize := by simpa only [growthLayout] using (saved_shape p hn).2.1
  have hb : (scratch p).toNat+16≤memory.byteSize := by
    rw [show memory.byteSize=(growthLayout p).memory.byteSize+(AllocateGrowth.delta (growthLayout p)).toNat*65536 from shapes.2.1,memorySize]
    exact ((scratch_numbers p hn).2.2.1).trans (Nat.le_add_right _ _)
  have hh : head.toNat+12≤memory.byteSize := by
    rw [show memory.byteSize=(growthLayout p).memory.byteSize+(AllocateGrowth.delta (growthLayout p)).toNat*65536 from shapes.2.1,←grow.2.1]
    exact grow.2.2.1
  have read := AllocateGrowth.finalMemory_record (growthLayout p) hn.growth
  have read0 : readI32 memory (scratch p).toNat=0 := by simpa only [memory,growthLayout] using read.1
  have read4 : readI32 memory ((scratch p).toNat+4)=head := by simpa only [memory,head,growthLayout] using read.2
  have h3m : mf.locals[3]?=some (.i32 (scratch p)) := by simp [mf,missedFrame,bf,emptyBlockFrame,h3]
  have fieldsC := checked_fields cfg s p
  have moduleC : (checked cfg s p).modules[mf.inst]?=some p.mi := by
    simp only [mf,missedFrame,bf,emptyBlockFrame]
    rw [fieldsC.2.1]
    exact hcode.originalCode.search.module
  have linkNext : WP cfg (fuel+249) (.next (atCode (linkFrom (checked cfg s p) op p.memoryIndex memory (scratch p) head) limits base.toArray (linkFrame mf head) callers WNear.Binary.AllocateRetry.secondAttempt)) (286*op+rest) post := by
    simpa only [linkFrom,linkNewFrom,linkOldFrom,relinked,oldLinked,op,memory,head,lf] using secondBridge
  have link := wp_relink cfg (fuel+249) (286*op+rest) (checked cfg s p) limits base.toArray mf callers WNear.Binary.AllocateRetry.secondAttempt
    (scratch p) head p.mi p.memoryIndex memory post h3m moduleC hcode.originalCode.search.memoryIndex (checked_memory cfg s p hmem) shapes.1 hb hh read4 (cc.mono (by simp only [op];omega)) linkNext
  have linkBridge : WP cfg (fuel+258) (.next (atCode (checked cfg s p) limits base.toArray mf callers
      (WNear.Binary.AllocateRetry.relink++WNear.Binary.AllocateRetry.secondAttempt))) (295*op+rest) post := by
    have cost : 9*cfg.regularOpCost+(286*op+rest)=295*op+rest := by simp only [op];omega
    simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using link
  have fieldsG := grown_fields cfg s p
  have moduleG : (grown cfg s p).modules[mf.inst]?=some p.mi := by
    simp only [mf,missedFrame,bf,emptyBlockFrame];rw [fieldsG.2.1];exact hcode.originalCode.search.module
  have checkNext : WP cfg (fuel+258) (.next (atCode (paid (grown cfg s p) op 5) limits base.toArray (missedFrame mf) callers
      (WNear.Binary.AllocateRetry.relink++WNear.Binary.AllocateRetry.secondAttempt))) (295*op+rest) post := by
    simpa only [checked,op,mf,missedFrame,Array.set!_eq_setIfInBounds,Array.setIfInBounds_setIfInBounds] using linkBridge
  have check := wp_record_check cfg (fuel+258) (295*op+rest) (grown cfg s p) limits base.toArray mf callers
    (WNear.Binary.AllocateRetry.relink++WNear.Binary.AllocateRetry.secondAttempt) (scratch p) p.mi p.memoryIndex memory post h3m moduleG
    hcode.originalCode.search.memoryIndex (grown_memory cfg s p hmem) (by omega) read0
    (cg.mono (by simp only [op];omega)) checkNext
  have cost : 5*cfg.regularOpCost+(295*op+rest)=300*cfg.regularOpCost+rest := by simp only [op];omega
  simpa only [cost,mf,bf,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using check
end WNear.Proofs.AllocateRetry
