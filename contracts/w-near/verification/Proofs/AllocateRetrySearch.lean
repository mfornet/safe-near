import Proofs.AllocateRetryAfterGrowth
import Proofs.AllocateRetryGrow

/-! Full real581 search block: empty result, growth, relink, and successful retry. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode grown checked relinked found prefixed firstAttempt firstMiss beforeGrow
  AllocateGrowth.callAfter AllocateFlagged.callAfter AllocateEmpty.callAfter growthLayout AllocateGrowth.delta memoryGrowCost

theorem wp_search_block (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h4 : frame.locals[4]?=some (.i32 (words p))) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (scratch p))) (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (582*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest))
    (hnext : WP cfg fuel (.next (atCode (found cfg s p) limits base.toArray (secondFrame frame p) callers code)) rest post) :
    WP cfg (fuel+439) (.next (atCode (prefixed s cfg.regularOpCost p) limits base.toArray frame callers
      (WNear.Binary.AllocatePositive.searchBlock++code)))
      (528*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))
  let bf := emptyBlockFrame frame base.toArray.size code
  let mf := missedFrame bf
  have cb : (beforeGrow s op p).host.gas.Credits (178*op+fee+(300*op+rest)) :=
    (gasUnits_beforeGrow s op p) _ (hc.mono (by simp only [op,fee];omega)) |>.2.2
  have cp : (prefixed s op p).host.gas.Credits (528*op+fee+rest) :=
    (gasUnits_prefixed s op p) _ (hc.mono (by simp only [op,fee];omega)) |>.2.2
  have cfirst : (firstAttempt s op p).host.gas.Credits (484*op+fee+rest) :=
    (gasUnits_firstAttempt s op p) _ (hc.mono (by simp only [op,fee];omega)) |>.2.2
  have cmiss : (firstMiss s op p).host.gas.Credits (482*op+fee+rest) := by
    unfold firstMiss
    exact paid_credits (firstAttempt s op p) op 2 (482*op+fee+rest) (cfirst.mono (by omega))
  have afterGrowth := wp_after_growth cfg fuel rest s limits base frame callers code p post hn hcode h4 h2 h3 hmem (by omega) hc hnext
  have growNext : WP cfg (fuel+263) (.next (atCode (Grow.after cfg (firstMiss s op p) p) limits base.toArray mf callers
      (WNear.Binary.AllocateRetry.growthCheck++WNear.Binary.AllocateRetry.relink++WNear.Binary.AllocateRetry.secondAttempt))) (300*op+rest) post := by
    simpa only [Grow.after,grown,beforeGrow,op,mf,bf] using afterGrowth
  have fields := beforeGrow_fields s op p
  have codeMiss : Code (firstMiss s op p) mf.inst p := by
    have fs : (firstMiss s op p).funcs=s.funcs ∧ (firstMiss s op p).modules=s.modules ∧ (firstMiss s op p).tables=s.tables := by
      simpa only [beforeGrow,paid,chargedStore] using fields
    simpa only [mf,missedFrame,bf,emptyBlockFrame] using hcode.transport s _ frame.inst p fs.1 fs.2.1 fs.2.2
  have memMiss : (firstMiss s op p).mems[p.memoryIndex]?=some (savedMemory p) := by
    simpa only [beforeGrow,paid,chargedStore] using beforeGrow_memory s op p hmem
  have h4m : mf.locals[4]?=some (.i32 (words p)) := by simp [mf,missedFrame,bf,emptyBlockFrame,h4]
  have h2m : mf.locals[2]?=some (.i32 1) := by simp [mf,missedFrame,bf,emptyBlockFrame,h2]
  have h3m : mf.locals[3]?=some (.i32 (scratch p)) := by simp [mf,missedFrame,bf,emptyBlockFrame,h3]
  have grow := Grow.wp_grow cfg (fuel+263) (300*op+rest) (firstMiss s op p) limits base mf callers
    (WNear.Binary.AllocateRetry.growthCheck++WNear.Binary.AllocateRetry.relink++WNear.Binary.AllocateRetry.secondAttempt) p post hn codeMiss
    h2m h3m h4m memMiss hd (cmiss.mono (by simp only [op,fee];omega)) growNext
  have growBridge : WP cfg (fuel+404) (.next (atCode (firstMiss s op p) limits base.toArray mf callers WNear.Binary.Allocate.retry)) (482*op+fee+rest) post := by
    have cost : 182*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+(300*op+rest)=482*op+fee+rest := by simp only [op,fee];omega
    rw [cost] at grow
    simpa only [WNear.Binary.AllocateRetry.retry_eq,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using grow
  have missNext : WP cfg (fuel+404) (.next (atCode (paid (firstAttempt s op p) op 2) limits base.toArray (missedFrame bf) callers WNear.Binary.Allocate.retry)) (482*op+fee+rest) post := by
    simpa only [firstMiss,mf] using growBridge
  have miss := wp_first_miss cfg (fuel+404) (482*op+fee+rest) (firstAttempt s op p) limits base.toArray bf callers WNear.Binary.Allocate.retry post
    (cfirst.mono (by simp only [op];omega)) missNext
  have emptyNext : WP cfg (fuel+406) (.next (atCode (emptyFrom (prefixed s op p) op) limits
      (base.toArray.push (.i32 0)) bf callers (.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry))) (484*op+fee+rest) post := by
    have cost : 2*cfg.regularOpCost+(482*op+fee+rest)=484*op+fee+rest := by simp only [op];omega
    rw [cost] at miss
    simpa only [emptyFrom,firstAttempt,Nat.add_assoc,Nat.reduceAdd] using miss
  have codePref : Code (prefixed s op p) bf.inst p := by
    have fs := AllocatePositive.prefixed_fields s op p.toLayout
    simpa only [prefixed,bf,emptyBlockFrame] using hcode.transport s (AllocatePositive.prefixed s op p.toLayout) frame.inst p fs.1 fs.2.1 fs.2.2
  have empty := wp_empty_attempt cfg (fuel+406) (484*op+fee+rest) (prefixed s op p) limits base bf callers
    (.local_tee 1::.br_if 0::WNear.Binary.Allocate.retry) p post hn h4 h2 h3 codePref (prefixed_memory s op p hmem) (by omega)
    (cp.mono (by simp only [op];omega)) emptyNext
  have blockNext : WP cfg (fuel+438) (.next (atCode (prefixed s op p) limits base.toArray bf callers
      (WNear.Binary.Allocate.attempt++[.local_tee 1,.br_if 0]++WNear.Binary.Allocate.retry))) (528*op+fee+rest) post := by
    have cost : 44*cfg.regularOpCost+(484*op+fee+rest)=528*op+fee+rest := by simp only [op];omega
    rw [cost] at empty
    simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using empty
  have block := wp_block_empty cfg (fuel+438) (528*op+fee+rest) (prefixed s op p) limits base.toArray frame callers
    (WNear.Binary.Allocate.attempt++[.local_tee 1,.br_if 0]++WNear.Binary.Allocate.retry) code post cp blockNext
  simpa only [WNear.Binary.AllocatePositive.searchBlock,op,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using block
end WNear.Proofs.AllocateRetry
