import Proofs.AllocateFlaggedResult
import Proofs.AllocateSearchEnter

/-! Actual complete f580 body on its nonempty, unflagged, directly-fitting
alignment-one branch. All heap facts refer to the original free-list metadata. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode searched searchAfter searchFrame candidateAfter splitAfter
  WNear.Binary.AllocateSearch.outer WNear.Binary.AllocateSearch.inspect

/-- All actual580 instructions, its two paid loop entries and its thirteen-label
exit. The returned pointer and memory are computed from the original heap. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : SearchCode s p frame.inst)
    (hw : frame.locals[0]?=some (.i32 p.words)) (ha : frame.locals[1]?=some (.i32 1))
    (hr : frame.locals[2]?=some (.i32 p.root)) (hctx : frame.locals[3]?=some (.i32 p.context))
    (hvt : frame.locals[4]?=some (.i32 p.vtable)) (hs : 14≤frame.locals.size)
    (hmem : s.mems[p.memoryIndex]?=some p.memory) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (262*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (searchAfter s cfg.regularOpCost p) limits
      (stack.push (.i32 (pointer p))) (searchFrame frame p) callers code)) rest post) :
    WP cfg (fuel+238) (.next (atCode s limits stack frame callers (WNear.Binary.Allocate.searchFunction.body++code)))
      (262*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let initial := initialAfter s op
  let f := initialFrame frame p
  let before := paid initial op 5
  let finished := searched before op p
  let final := searchedFrame f p
  have fi := initialFrame_locals frame p hs
  have fo := initialFrame_original frame p
  have sz : 14≤f.locals.size := by simpa only [f,initialFrame,Array.size_set!] using hs
  have ready : CandidateReady f p := by
    exact ⟨fo.1.trans hw,fi.1,fo.2.2.1.trans hctx,fo.2.2.2.trans hvt,fi.2.2.1,fi.2.2.2.2,sz⟩
  have ci : initial.host.gas.Credits (246*op+rest) := initialAfter_credits s op _ (hc.mono (by dsimp [op]; omega))
  have cb : before.host.gas.Credits (240*op+(op+rest)) := paid_credits initial op 5 _ (ci.mono (by omega))
  have cf : finished.host.gas.Credits (op+rest) := searched_credits before op (op+rest) p cb
  have finalPointer : final.locals[5]?=some (.i32 (pointer p)) := by
    have eq := (Allocate.split_result p.memory (head p) p.words hn.split).1
    have value : header p+8=pointer p := eq
    simpa only [final,value] using searchedFrame_pointer f p sz
  have getNext : WP cfg fuel (.next (atCode (chargedStore finished cfg.regularOpCost) limits
      (stack.push (.i32 (pointer p))) final callers code)) rest post := by
    simpa only [searchAfter,searchFrame,initial,before,finished,final,f,paid,op] using hnext
  have get := wp_local_get cfg fuel rest finished limits stack final callers code 5 (.i32 (pointer p)) post finalPointer cf getNext
  let label : Label := ⟨0,stack.size,.local_get 5::code,none⟩
  have endNext : WP cfg (fuel+1) (.next (atCode finished limits stack final callers label.rest)) (op+rest) post := get
  have endBlock := wp_end_label cfg (fuel+1) (op+rest) finished limits stack final callers label post cf endNext
  have inspectNext : WP cfg (fuel+2) (.next (atCode (searched before op p) limits stack
      (outerFrame (searchedFrame f p) stack.size code) callers [])) (op+rest) post := by
    simpa only [outerFrame,emptyBlockFrame,label,final,finished,Nat.add_assoc,Nat.reduceAdd] using endBlock
  have baseCode := hcode.toCode.paid s op 21 p frame.inst
  have inst : f.inst=frame.inst := rfl
  have codeBefore : SearchCode before p f.inst := by
    rw [inst]
    have modulePaid : Code before p frame.inst := by
      simpa only [before,initial,initialAfter,ValueReturnBorrow.paid_add,Nat.reduceAdd] using baseCode
    exact {modulePaid with
      sizeIndex:=hcode.sizeIndex
      sizeFunction:=by simpa only [before,initial,initialAfter,paid,chargedStore] using hcode.sizeFunction}
  have memBefore : before.mems[p.memoryIndex]?=some p.memory := by simpa only [before,initial,initialAfter,paid,chargedStore] using hmem
  have inspect := wp_inspect_success cfg (fuel+2) (op+rest) before limits stack f callers code p post hn ready codeBefore memBefore hd cb inspectNext
  have enterNext : WP cfg (fuel+211) (.next (atCode (paid initial op 5) limits stack (inspectFrame f stack.size code) callers
      WNear.Binary.AllocateSearch.inspect)) (241*op+rest) post := by
    have cost : 240*cfg.regularOpCost+(op+rest)=241*op+rest := by dsimp [op]; omega
    rw [cost] at inspect
    simpa only [before,Nat.add_assoc,Nat.reduceAdd] using inspect
  have entered := wp_enter_search cfg (fuel+211) (241*op+rest) initial limits stack f callers code p post hn.headNonzero fi.1
    (ci.mono (by dsimp [op]; omega)) enterNext
  have initialNext : WP cfg (fuel+222) (.next (atCode initial limits stack f callers
      (.block .empty WNear.Binary.AllocateSearch.outer::.local_get 5::code))) (246*op+rest) post := by
    have cost : 5*cfg.regularOpCost+(241*op+rest)=246*op+rest := by dsimp [op]; omega
    rw [cost] at entered
    simpa only [Nat.add_assoc,Nat.reduceAdd] using entered
  have result := wp_initial cfg (fuel+222) (246*op+rest) s limits stack frame callers
    (.block .empty WNear.Binary.AllocateSearch.outer::.local_get 5::code) p post ha hr hcode.module hcode.memoryIndex hmem hn.rootBound
    (hc.mono (by dsimp [op]; omega)) initialNext
  have cost : 16*cfg.regularOpCost+(246*op+rest)=262*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  rw [WNear.Binary.AllocateSearch.function_body]
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.append_eq,List.cons_append,List.nil_append] using result
end
end WNear.Proofs.AllocateFlagged
