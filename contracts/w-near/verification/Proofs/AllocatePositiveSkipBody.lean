import Proofs.AllocatePositiveSkipSearch
import Proofs.AllocatePositiveGuard
import Proofs.AllocatePositiveHead
import Proofs.AllocatePositiveSkipRestore
import Proofs.AllocatePositiveSkipResources
import Proofs.AllocatePositiveSkipGas

/-! Full actual positive581 path whose first580 call skips one short node, then fits. The
saved head and final head write are sequential; no separation is assumed. -/
namespace WNear.Proofs.AllocatePositiveSkip
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocatePositive (wp_positive_guard wp_update_head updateFrom)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode reserved prefixed searched found updated after Allocate.prefixAfter AllocateSkip.callAfter

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.allocator)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 5≤frame.locals.size)
    (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hglobal : s.globals[p.globalIndex]?=some p.global) (hsp : p.global.value=.i32 p.sp)
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (417*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits
      (base.toArray.push (.i32 (result p))) (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+356) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Allocate.function.body++code)))
      (417*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  let pf := prefixFrame frame p
  let ff := resultFrame frame p
  let r := reserved s op p
  let guarded := paid r op 2
  let pr := prefixed s op p
  let f := found s op p
  let u := updated s op p
  let tail := WNear.Binary.AllocatePositive.restore++code
  have scratchFacts := scratch_numbers p hn
  have v1 : 1<frame.locals.size := by omega
  have v3 : 3<frame.locals.size := by omega
  have v4 : 4<frame.locals.size := by omega
  have h3rf : rf.locals[3]?=some (.i32 (scratch p)) := by simp [rf,reservedFrame,v3]
  have ff0 : ff.locals[0]?=some (.i32 p.allocator) := by simp [ff,resultFrame,prefixFrame,Allocate.roundedFrame,reservedFrame,h0]
  have ff1 : ff.locals[1]?=some (.i32 (result p)) := by simp [ff,resultFrame,prefixFrame,Allocate.roundedFrame,reservedFrame,v1]
  have ff3 : ff.locals[3]?=some (.i32 (scratch p)) := by simp [ff,resultFrame,prefixFrame,Allocate.roundedFrame,reservedFrame,v3]
  have instRF : rf.inst=frame.inst := rfl
  have instPF : pf.inst=frame.inst := rfl
  have instFF : ff.inst=frame.inst := rfl
  have cu := updated_credits s op (5*op+rest) p (hc.mono (by dsimp [op]; omega))
  have cf := found_credits s op (9*op+rest) p (hc.mono (by dsimp [op]; omega))
  have cp := prefixed_credits s op (363*op+rest) p (hc.mono (by dsimp [op]; omega))
  have cr := reserved_credits s op (412*op+rest) p (hc.mono (by dsimp [op]; omega))
  have codeU := updated_code s op frame.inst p hcode
  have moduleU : u.modules[ff.inst]?=some p.mi := by rw [instFF]; exact codeU.search.module
  have globalU : u.globals[p.globalIndex]?=some {p.global with value:=.i32 (scratch p)} := by
    rw [updated_globals]
    simp only [setGlobal,Array.getElem?_modify,hglobal,Option.map_some,ite_true]
  have restoreNext : WP cfg fuel (.next (atCode (restoreFrom u cfg.regularOpCost p.globalIndex p.sp) limits
      (base.toArray.push (.i32 (result p))) ff callers code)) rest post := by
    simpa only [restoreFrom,after,u,ff,op] using hnext
  have restore := wp_restore_result cfg fuel rest u limits base.toArray ff callers code p {p.global with value:=.i32 (scratch p)} post
    ff3 ff1 moduleU hcode.globalIndex globalU scratchFacts.2.2.2 cu restoreNext
  let label : Label := ⟨0,base.toArray.size,tail,none⟩
  have endNext : WP cfg (fuel+5) (.next (atCode u limits base.toArray ff callers label.rest)) (5*op+rest) post := restore
  have endBlock := wp_end_label cfg (fuel+5) (5*op+rest) u limits base.toArray ff callers label post cu endNext
  have codeF := found_code s op frame.inst p hcode
  have moduleF : f.modules[(emptyBlockFrame ff base.toArray.size tail).inst]?=some p.mi := by
    simp only [emptyBlockFrame,instFF]
    exact codeF.search.module
  have headNext : WP cfg (fuel+6) (.next (atCode (updateFrom f cfg.regularOpCost p.memoryIndex (searchedMemory p) p.allocator (scratch p)) limits
      base.toArray (emptyBlockFrame ff base.toArray.size tail) callers [])) (5*op+rest) post := by
    simpa only [updateFrom,updated,f,u,label,ff,emptyBlockFrame,op,Nat.add_assoc,Nat.reduceAdd] using endBlock
  have memF := found_memory s op p hmem
  have sizeFinal := searchedMemory_size p hn
  have head := wp_update_head cfg (fuel+6) (5*op+rest) f limits base.toArray (emptyBlockFrame ff base.toArray.size tail) callers []
    p.mi p.memoryIndex (searchedMemory p) p.allocator (scratch p) post ff0 ff3 moduleF hcode.search.memoryIndex memF
    (by rw [sizeFinal]; exact hn.allocatorBound) (by rw [sizeFinal]; exact scratchFacts.2.2.1)
    (cf.mono (by dsimp [op]; omega)) headNext
  have codeP := prefixed_code s op frame.inst p hcode
  have searchCode : Code pr (emptyBlockFrame pf base.toArray.size tail).inst p := by
    simp only [emptyBlockFrame,instPF]; exact codeP
  have searchNext : WP cfg (fuel+10) (.next (atCode (foundAfter pr cfg.regularOpCost p) limits base.toArray
      (foundFrame (emptyBlockFrame pf base.toArray.size tail) p) callers WNear.Binary.AllocatePositive.updateHead)) (9*op+rest) post := by
    have cost : 4*cfg.regularOpCost+(5*op+rest)=9*op+rest := by dsimp [op]; omega
    rw [cost] at head
    simpa only [foundAfter,attemptAfter,found,searched,prefixed,pr,f,foundFrame,ff,resultFrame,pf,emptyBlockFrame,List.append_nil,
      Nat.add_assoc,Nat.reduceAdd,op] using head
  have pf4 : pf.locals[4]?=some (.i32 (words p)) := by simp [pf,prefixFrame,Allocate.roundedFrame,reservedFrame,words,v4]
  have pf2 : pf.locals[2]?=some (.i32 1) := by simp [pf,prefixFrame,Allocate.roundedFrame,reservedFrame,h2]
  have pf3 : pf.locals[3]?=some (.i32 (scratch p)) := by simp [pf,prefixFrame,Allocate.roundedFrame,reservedFrame,v3]
  have search := wp_first_search cfg (fuel+10) (9*op+rest) pr limits base (emptyBlockFrame pf base.toArray.size tail) callers
    WNear.Binary.AllocatePositive.updateHead p post hn pf4 pf2 pf3 searchCode (prefixed_memory s op p hmem) hd (cp.mono (by dsimp [op]; omega)) searchNext
  have prefixNext : WP cfg (fuel+316) (.next (atCode pr limits base.toArray
      (Allocate.roundedFrame (emptyBlockFrame rf base.toArray.size tail) p.size) callers
      (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) (363*op+rest) post := by
    have cost : 354*cfg.regularOpCost+(9*op+rest)=363*op+rest := by dsimp [op]; omega
    rw [cost] at search
    simpa only [pf,prefixFrame,emptyBlockFrame,Allocate.roundedFrame,Nat.add_assoc,Nat.reduceAdd] using search
  have codeR : Code r frame.inst p := by
    have fs := reserved_fields s op p
    exact hcode.transport s r frame.inst p fs.1 fs.2.1 fs.2.2
  have codeG := codeR.paid r op 2 frame.inst p
  have moduleG : guarded.modules[(emptyBlockFrame rf base.toArray.size tail).inst]?=some p.mi := by
    simp only [emptyBlockFrame,instRF]
    exact codeG.search.module
  have memG : guarded.mems[p.memoryIndex]?=some p.memory := by simpa only [guarded,r,reserved,paid,chargedStore,setGlobal] using hmem
  have guardedCredits := paid_credits r op 2 (410*op+rest) (cr.mono (by omega))
  have prefixBridge : WP cfg (fuel+316) (.next (atCode (Allocate.prefixAfter guarded cfg.regularOpCost p.memoryIndex (scratch p) p.allocator p.memory) limits base.toArray
      (Allocate.roundedFrame (emptyBlockFrame rf base.toArray.size tail) p.size) callers
      (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) (363*op+rest) post := by
    simpa only [prefixed,pr,guarded,r,op] using prefixNext
  have prefixProof := Allocate.wp_align_and_save cfg (fuel+316) (363*op+rest) guarded limits base (emptyBlockFrame rf base.toArray.size tail) callers
    (WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead) p.size (scratch p) p.allocator p.mi p.memoryIndex p.alignAddress p.roundAddress p.memory post
    (by simpa [rf,reservedFrame,emptyBlockFrame] using h1) h3rf (by simpa [rf,reservedFrame,emptyBlockFrame] using h0)
    moduleG hcode.search.memoryIndex memG hn.allocatorBound scratchFacts.2.2.1 codeG.alignIndex codeG.alignFunction codeG.roundIndex codeG.roundFunction
    hn.rounding hd (guardedCredits.mono (by dsimp [op]; omega)) prefixBridge
  have guardNext : WP cfg (fuel+347) (.next (atCode guarded limits base.toArray (emptyBlockFrame rf base.toArray.size tail) callers
      (WNear.Binary.Allocate.alignAndSave++WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead))) (410*op+rest) post := by
    have cost : 47*cfg.regularOpCost+(363*op+rest)=410*op+rest := by dsimp [op]; omega
    rw [cost] at prefixProof
    simpa only [prefixed,pr,guarded,r,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using prefixProof
  have guard := wp_positive_guard cfg (fuel+347) (410*op+rest) r limits base.toArray (emptyBlockFrame rf base.toArray.size tail) callers
    (WNear.Binary.Allocate.alignAndSave++WNear.Binary.AllocatePositive.searchBlock++WNear.Binary.AllocatePositive.updateHead) p.size post
    (by simpa [rf,reservedFrame,emptyBlockFrame] using h1) hn.positive (cr.mono (by dsimp [op]; omega)) guardNext
  have outerNext : WP cfg (fuel+350) (.next (atCode r limits base.toArray (emptyBlockFrame rf base.toArray.size tail) callers
      WNear.Binary.AllocatePositive.positive)) (412*op+rest) post := by
    have cost : 2*cfg.regularOpCost+(410*op+rest)=412*op+rest := by dsimp [op]; omega
    rw [cost] at guard
    simpa only [WNear.Binary.AllocatePositive.positive,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using guard
  have outer := wp_block_empty cfg (fuel+350) (412*op+rest) r limits base.toArray rf callers WNear.Binary.AllocatePositive.positive tail post cr outerNext
  have reserveNext : WP cfg (fuel+351) (.next (atCode (setGlobal (paid s cfg.regularOpCost 5) p.globalIndex (.i32 (p.sp-16))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.sp-16))} callers (.block .empty WNear.Binary.AllocatePositive.positive::tail))) (412*op+rest) post := by
    simpa only [r,reserved,rf,reservedFrame,scratch,Nat.add_assoc,Nat.reduceAdd] using outer
  have reserve := ValueReturnBorrow.wp_reserve cfg (fuel+351) (412*op+rest) s limits base.toArray frame callers
    (.block .empty WNear.Binary.AllocatePositive.positive::tail) p.mi p.globalIndex p.global p.sp 3 post hcode.search.module hcode.globalIndex hglobal hsp
    (hc.mono (by dsimp [op]; omega)) reserveNext
  have cost : 5*cfg.regularOpCost+(412*op+rest)=417*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at reserve
  rw [WNear.Binary.AllocatePositive.body_eq]
  simpa only [WNear.Binary.AllocatePositive.reserve,tail,Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using reserve
end WNear.Proofs.AllocatePositiveSkip
