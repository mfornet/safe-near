import Proofs.AllocateSkipCandidate
import Proofs.AllocateSkipFrame

/-! Complete actual one-candidate hop, from inspect to the next inspect. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
attribute [local irreducible] WP atCode candidateAfter advanced hopped resumed advanceStore
set_option maxRecDepth 16384

 theorem wp_hop (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : SearchCode s p frame.inst)
    (hh : frame.locals[1]?=some (.i32 (head p))) (hw : frame.locals[0]?=some (.i32 p.words))
    (hr : frame.locals[2]?=some (.i32 p.root)) (hs : 14≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (71*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (resumed s cfg.regularOpCost p) limits stack
      (inspectFrame (hopFrame frame p) stack.size code) callers WNear.Binary.AllocateSearch.inspect)) rest post) :
    WP cfg (fuel+59) (.next (atCode s limits stack (inspectFrame frame stack.size code) callers WNear.Binary.AllocateSearch.inspect))
      (71*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let cf := candidateFrame frame p
  let hf := hopFrame frame p
  have headNext : hf.locals[1]?=some (.i32 (head (nextLayout p))) := by
    rw [nextLayout_head p hn]
    simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,show 1<frame.locals.size by omega]
  have scanNext : WP cfg fuel (.next (atCode (paid (hopped s op p) cfg.regularOpCost 4) limits stack
      (inspectFrame hf stack.size code) callers WNear.Binary.AllocateSearch.inspect)) rest post := by
    simpa only [resumed,hf,op] using hnext
  have scan := wp_scan_nonempty cfg fuel rest (hopped s op p) limits stack hf callers code (nextLayout p) post
    (native_next p hn).headNonzero headNext (hopped_credits s op (4*op+rest) p (hc.mono (by dsimp [op];omega))) scanNext
  have advanceNext : WP cfg (fuel+8) (.next (atCode (advanceStore (candidateAfter s op) op p) limits stack
      (scanFrame (advanceFrame cf p) stack.size code) callers WNear.Binary.AllocateSearch.scan)) (4*op+rest) post := by
    simpa only [advanceStore,hopped,advanced,hf,hopFrame,cf,advanceFrame,op] using scan
  have cr := candidateAfter_credits s op (11*op+rest) (hc.mono (by dsimp [op];omega))
  have fs := candidate_fields s op
  have cm : (candidateAfter s op).modules[cf.inst]?=some p.mi := by
    rw [fs.2.1]
    simpa only [cf,candidateFrame,unitsFrame,prepareFrame] using hcode.module
  have mem : (candidateAfter s op).mems[p.memoryIndex]?=some p.memory := by rw [candidate_mems];exact hm
  have rootLocal : cf.locals[2]?=some (.i32 p.root) := by simp [cf,candidateFrame,unitsFrame,prepareFrame,hr]
  have linkLocal : cf.locals[9]?=some (.i32 (head p+8)) := by simp [cf,candidateFrame,unitsFrame,prepareFrame,show 9<frame.locals.size by omega]
  have advance := wp_advance cfg (fuel+8) (4*op+rest) (candidateAfter s op) limits stack cf callers code p post hn
    rootLocal linkLocal cm hcode.memoryIndex mem (cr.mono (by dsimp [op];omega)) advanceNext
  have cn : WP cfg (fuel+14) (.next (atCode (candidateAfter s op) limits stack (shortFrame cf stack.size code) callers WNear.Binary.AllocateSkip.advance))
      (11*op+rest) post := by
    have fee : 7*cfg.regularOpCost+(4*op+rest)=11*op+rest := by dsimp [op];omega
    simpa only [shortFrame,Nat.add_assoc,Nat.reduceAdd,fee] using advance
  have first := wp_candidate_short cfg (fuel+14) (11*op+rest) s limits stack frame callers code p post hn hcode hh hw hs hm hd
    (hc.mono (by dsimp [op];omega)) cn
  have fee : 60*cfg.regularOpCost+(11*op+rest)=71*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [fee,Nat.add_assoc,Nat.reduceAdd] using first
end
end WNear.Proofs.AllocateSkip
