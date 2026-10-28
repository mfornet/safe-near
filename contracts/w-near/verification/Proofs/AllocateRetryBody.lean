import Proofs.AllocateRetrySearch
import Proofs.AllocateRetryPrefix
import Proofs.AllocateRetrySuffix

/-! Full real581 growth-and-retry body on its original empty-list domain. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode prefixed found after growthLayout AllocateGrowth.delta memoryGrowCost

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.allocator)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 5≤frame.locals.size)
    (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hd : callers.length+3<limits.maxCallDepth)
    (hc : s.host.gas.Credits (591*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits (base.toArray.push (.i32 (result p))) (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+489) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Allocate.function.body++code)))
      (591*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest) post := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))
  let cf := continuationFrame frame p base.toArray.size code
  let ff := resultFrame frame p
  have v1 : 1<frame.locals.size := by omega
  have v3 : 3<frame.locals.size := by omega
  have v4 : 4<frame.locals.size := by omega
  have f0 : ff.locals[0]?=some (.i32 p.allocator) := by simp [ff,resultFrame,prefixFrame,AllocatePositive.prefixFrame,AllocatePositive.reservedFrame,Allocate.roundedFrame,h0]
  have f1 : ff.locals[1]?=some (.i32 (result p)) := by simp [ff,resultFrame,prefixFrame,AllocatePositive.prefixFrame,AllocatePositive.reservedFrame,Allocate.roundedFrame,v1]
  have f3 : ff.locals[3]?=some (.i32 (scratch p)) := by simp [ff,resultFrame,prefixFrame,AllocatePositive.prefixFrame,AllocatePositive.reservedFrame,Allocate.roundedFrame,v3,scratch,AllocatePositive.scratch]
  have codeF : Code s ff.inst p := by simpa only [ff,resultFrame,prefixFrame,AllocatePositive.prefixFrame,AllocatePositive.reservedFrame,Allocate.roundedFrame] using hcode
  have cfound : (found cfg s p).host.gas.Credits (9*op+rest) :=
    (found_gas cfg s p).credits (hc.mono (by simp only [op];omega))
  have suffix := wp_suffix cfg fuel rest s limits base ff callers code p post hn codeF f0 f1 f3 hmem hg hv cfound hnext
  have searchNext : WP cfg (fuel+10) (.next (atCode (found cfg s p) limits base.toArray (secondFrame cf p) callers WNear.Binary.AllocatePositive.updateHead)) (9*op+rest) post := by
    simpa only [cf,ff,continuationFrame,secondFrame,resultFrame,prefixFrame,AllocatePositive.prefixFrame,Allocate.roundedFrame,emptyBlockFrame] using suffix
  have c4 : cf.locals[4]?=some (.i32 (words p)) := by simp [cf,continuationFrame,Allocate.roundedFrame,AllocatePositive.reservedFrame,emptyBlockFrame,v4,words,AllocatePositive.words]
  have c2 : cf.locals[2]?=some (.i32 1) := by simp [cf,continuationFrame,Allocate.roundedFrame,AllocatePositive.reservedFrame,emptyBlockFrame,h2]
  have c3 : cf.locals[3]?=some (.i32 (scratch p)) := by simp [cf,continuationFrame,Allocate.roundedFrame,AllocatePositive.reservedFrame,emptyBlockFrame,v3,scratch,AllocatePositive.scratch]
  have codeC : Code s cf.inst p := by simpa only [cf,continuationFrame,Allocate.roundedFrame,AllocatePositive.reservedFrame,emptyBlockFrame] using hcode
  have search := wp_search_block cfg (fuel+10) (9*op+rest) s limits base cf callers WNear.Binary.AllocatePositive.updateHead p post hn codeC c4 c2 c3 hmem hd
    (hc.mono (by simp only [op];omega)) searchNext
  have prefixNext : WP cfg (fuel+449) (.next (atCode (prefixed s op p) limits base.toArray cf callers
      (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) (537*op+fee+rest) post := by
    have cost : 528*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+(9*op+rest)=537*op+fee+rest := by simp only [op,fee];omega
    rw [cost] at search
    simpa only [Nat.add_assoc,Nat.reduceAdd] using search
  have result := wp_prefix cfg (fuel+449) (537*op+fee+rest) s limits base frame callers code p post hn hcode h0 h1 hs hmem hg hv (by omega)
    (hc.mono (by simp only [op,fee];omega)) prefixNext
  have cost : 54*cfg.regularOpCost+(537*op+fee+rest)=591*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest := by simp only [op,fee];omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocateRetry
