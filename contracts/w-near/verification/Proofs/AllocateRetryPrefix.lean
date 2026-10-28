import Proofs.AllocateRetryDomain
import Proofs.AllocatePositiveResources
import Proofs.AllocatePositiveGuard
import Proofs.AllocateRetryGas

/-! Real581 reserve, positive guard, alignment and original-head save prefix. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved prefixed Allocate.prefixAfter

def continuationFrame (frame : CallFrame) (p : Layout) (height : Nat) (code : Expr) :=
  Allocate.roundedFrame (emptyBlockFrame (AllocatePositive.reservedFrame frame p.toLayout) height
    (WNear.Binary.AllocatePositive.restore++code)) p.size

theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.allocator)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (hs : 5≤frame.locals.size) (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (54*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (prefixed s cfg.regularOpCost p) limits base.toArray
      (continuationFrame frame p base.toArray.size code) callers
      (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) rest post) :
    WP cfg (fuel+40) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.Allocate.function.body++code))) (54*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := AllocatePositive.reservedFrame frame p.toLayout
  let r := reserved s op p
  let guarded := paid r op 2
  let tail := WNear.Binary.AllocatePositive.restore++code
  have scratchFacts := scratch_numbers p hn
  have v3 : 3<frame.locals.size := by omega
  have h3rf : rf.locals[3]?=some (.i32 (scratch p)) := by simp [rf,AllocatePositive.reservedFrame,scratch,v3]
  have instRF : rf.inst=frame.inst := rfl
  have cr : r.host.gas.Credits (49*op+rest) := gasUnits_reserved s op p (49*op+rest) (hc.mono (by dsimp [op];omega)) |>.2.2
  have fs : r.funcs=s.funcs ∧ r.modules=s.modules ∧ r.tables=s.tables := by
    simpa only [r,reserved] using AllocatePositive.reserved_fields s op p.toLayout
  have codeR := hcode.originalCode.transport s r frame.inst p.toLayout fs.1 fs.2.1 fs.2.2
  have codeG := codeR.paid r op 2 frame.inst p.toLayout
  have moduleG : guarded.modules[(emptyBlockFrame rf base.toArray.size tail).inst]?=some p.mi := by
    simp only [emptyBlockFrame,instRF]
    exact codeG.search.module
  have memG : guarded.mems[p.memoryIndex]?=some p.memory := by
    simpa only [guarded,r,reserved,AllocatePositive.reserved,paid,chargedStore,setGlobal] using hmem
  have guardedCredits := paid_credits r op 2 (47*op+rest) (cr.mono (by omega))
  have prefixBridge : WP cfg fuel (.next (atCode (Allocate.prefixAfter guarded cfg.regularOpCost p.memoryIndex (scratch p) p.allocator p.memory)
      limits base.toArray (Allocate.roundedFrame (emptyBlockFrame rf base.toArray.size tail) p.size) callers
      (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) rest post := by
    simpa only [prefixed,AllocatePositive.prefixed,reserved,AllocatePositive.reserved,continuationFrame,rf,guarded,r,scratch,tail,op] using hnext
  have prefixProof := Allocate.wp_align_and_save cfg fuel rest guarded limits base (emptyBlockFrame rf base.toArray.size tail) callers
    (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead) p.size (scratch p) p.allocator p.mi p.memoryIndex
    p.alignAddress p.roundAddress p.memory post
    (by simpa [rf,AllocatePositive.reservedFrame,emptyBlockFrame] using h1) h3rf
    (by simpa [rf,AllocatePositive.reservedFrame,emptyBlockFrame] using h0)
    moduleG hcode.originalCode.search.memoryIndex memG hn.allocatorBound scratchFacts.2.2.1
    codeG.alignIndex codeG.alignFunction codeG.roundIndex codeG.roundFunction hn.rounding hd guardedCredits prefixBridge
  have guardNext : WP cfg (fuel+31) (.next (atCode guarded limits base.toArray (emptyBlockFrame rf base.toArray.size tail) callers
      (WNear.Binary.Allocate.alignAndSave++WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) (47*op+rest) post := by
    simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc,op] using prefixProof
  have guard := AllocatePositive.wp_positive_guard cfg (fuel+31) (47*op+rest) r limits base.toArray
    (emptyBlockFrame rf base.toArray.size tail) callers
    (WNear.Binary.Allocate.alignAndSave++WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead) p.size post
    (by simpa [rf,AllocatePositive.reservedFrame,emptyBlockFrame] using h1) hn.positive (cr.mono (by dsimp [op];omega)) guardNext
  have outerNext : WP cfg (fuel+34) (.next (atCode r limits base.toArray (emptyBlockFrame rf base.toArray.size tail) callers
      WNear.Binary.AllocatePositive.positive)) (49*op+rest) post := by
    have ce : 2*cfg.regularOpCost+(47*op+rest)=49*op+rest := by dsimp [op];omega
    simpa only [ce,WNear.Binary.AllocatePositive.positive,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using guard
  have outer := wp_block_empty cfg (fuel+34) (49*op+rest) r limits base.toArray rf callers WNear.Binary.AllocatePositive.positive tail post cr outerNext
  have reserveNext : WP cfg (fuel+35) (.next (atCode (setGlobal (paid s cfg.regularOpCost 5) p.globalIndex (.i32 (p.sp-16))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.sp-16))} callers (.block .empty WNear.Binary.AllocatePositive.positive::tail))) (49*op+rest) post := by
    simpa only [r,reserved,AllocatePositive.reserved,rf,AllocatePositive.reservedFrame,scratch,AllocatePositive.scratch,Nat.add_assoc,Nat.reduceAdd] using outer
  have reserve := ValueReturnBorrow.wp_reserve cfg (fuel+35) (49*op+rest) s limits base.toArray frame callers
    (.block .empty WNear.Binary.AllocatePositive.positive::tail) p.mi p.globalIndex p.global p.sp 3 post
    hcode.originalCode.search.module hcode.originalCode.globalIndex hg hv (hc.mono (by dsimp [op];omega)) reserveNext
  have ce : 5*cfg.regularOpCost+(49*op+rest)=54*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  rw [WNear.Binary.AllocatePositive.body_eq]
  simpa only [WNear.Binary.AllocatePositive.reserve,tail,Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using reserve
end WNear.Proofs.AllocateRetry
