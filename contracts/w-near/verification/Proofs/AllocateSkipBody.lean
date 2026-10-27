import Proofs.AllocateSkipHop
import Proofs.AllocateSearchBody

/-! Whole actual580 body after one short-node hop and the proved next-node split. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode resumed hopped candidateAfter AllocateSearch.searched

def before (s : Store NearState) (op : Nat) := paid (initialAfter s op) op 5
def after (s : Store NearState) (op : Nat) (p : Layout) := paid (AllocateSearch.searched (resumed (before s op) op p) op (nextLayout p)) op 1
def finalFrame (frame : CallFrame) (p : Layout) := AllocateSearch.searchedFrame (hopFrame (initialFrame frame p) p) (nextLayout p)

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (329*op+rest)) :
    (after s op p).host.gas.Credits rest := by
  have a := initialAfter_credits s op (313*op+rest) (hc.mono (by omega))
  have b := paid_credits (initialAfter s op) op 5 (308*op+rest) (a.mono (by omega))
  have c := resumed_credits (before s op) op (237*op+rest) p (b.mono (by omega))
  have d := searched_credits (resumed (before s op) op p) op (op+rest) (nextLayout p) (c.mono (by omega))
  exact paid_credits (AllocateSearch.searched (resumed (before s op) op p) op (nextLayout p)) op 1 rest (by simpa only [Nat.one_mul] using d)

 theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : SearchCode s p frame.inst)
    (hw : frame.locals[0]?=some (.i32 p.words)) (ha : frame.locals[1]?=some (.i32 1))
    (hr : frame.locals[2]?=some (.i32 p.root)) (hctx : frame.locals[3]?=some (.i32 p.context))
    (hvt : frame.locals[4]?=some (.i32 p.vtable)) (hs : 14≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (329*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits (stack.push (.i32 (pointer (nextLayout p))))
      (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel+294) (.next (atCode s limits stack frame callers (WNear.Binary.Allocate.searchFunction.body++code)))
      (329*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let initial := initialAfter s op
  let f := initialFrame frame p
  let hopInput := before s op
  let hf := hopFrame f p
  let nextStore := resumed hopInput op p
  let final := AllocateSearch.searchedFrame hf (nextLayout p)
  let finished := AllocateSearch.searched nextStore op (nextLayout p)
  have fi := initialFrame_locals frame p hs
  have fo := initialFrame_original frame p
  have initialSize : 14≤f.locals.size := by simpa only [f,initialFrame,Array.size_set!] using hs
  have hopReady : CandidateReady hf (nextLayout p) := by
    constructor
    · simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,f,initialFrame,nextLayout,hw]
    · rw [nextLayout_head p hn]
      simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,f,initialFrame,show 1<frame.locals.size by omega]
    · simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,f,initialFrame,nextLayout,hctx]
    · simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,f,initialFrame,nextLayout,hvt]
    · simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,f,initialFrame,show 6<frame.locals.size by omega]
    · simp [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,f,initialFrame,show 8<frame.locals.size by omega]
    · simpa only [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame,Array.size_set!] using initialSize
  have c16 := initialAfter_credits s op (313*op+rest) (hc.mono (by dsimp [op];omega))
  have c21 : hopInput.host.gas.Credits (308*op+rest) := paid_credits initial op 5 _ (c16.mono (by omega))
  have c92 : nextStore.host.gas.Credits (237*op+rest) := resumed_credits hopInput op _ p (c21.mono (by omega))
  have c328 : finished.host.gas.Credits (op+rest) := searched_credits nextStore op (op+rest) (nextLayout p) (c92.mono (by omega))
  have nextNative := native_next p hn
  have pointerLocal : final.locals[5]?=some (.i32 (pointer (nextLayout p))) := by
    have eq := (Allocate.split_result (nextLayout p).memory (head (nextLayout p)) p.words nextNative.split).1
    have value : AllocateSearch.header (nextLayout p)+8=pointer (nextLayout p) := eq
    have loc := searchedFrame_pointer hf (nextLayout p) hopReady.size
    simpa only [final,value] using loc
  have gn : WP cfg fuel (.next (atCode (chargedStore finished cfg.regularOpCost) limits (stack.push (.i32 (pointer (nextLayout p)))) final callers code)) rest post := by
    simpa only [after,finalFrame,before,hopInput,hf,f,nextStore,finished,final,paid,op] using hnext
  have get := wp_local_get cfg fuel rest finished limits stack final callers code 5 (.i32 (pointer (nextLayout p))) post pointerLocal c328 gn
  let label : Label := ⟨0,stack.size,.local_get 5::code,none⟩
  have blockNext : WP cfg (fuel+1) (.next (atCode finished limits stack final callers label.rest)) (op+rest) post := get
  have endBlock := wp_end_label cfg (fuel+1) (op+rest) finished limits stack final callers label post c328 blockNext
  have inspectNext : WP cfg (fuel+2) (.next (atCode finished limits stack (outerFrame final stack.size code) callers [])) (op+rest) post := by
    simpa only [outerFrame,emptyBlockFrame,label,Nat.add_assoc,Nat.reduceAdd] using endBlock
  have beforeCode : SearchCode hopInput p f.inst := by
    have modulePaid := hcode.toCode.paid s op 21 p frame.inst
    have instEq : f.inst=frame.inst := by simp only [f,initialFrame]
    rw [instEq]
    have beforeBase : Code hopInput p frame.inst := by
      simpa only [hopInput,before,initialAfter,ValueReturnBorrow.paid_add,Nat.reduceAdd] using modulePaid
    exact {beforeBase with sizeIndex:=hcode.sizeIndex,sizeFunction:=by simpa only [hopInput,before,initialAfter,paid,chargedStore] using hcode.sizeFunction}
  have nextCode : SearchCode nextStore (nextLayout p) hf.inst := by
    have instEq : hf.inst=f.inst := by simp only [hf,hopFrame,candidateFrame,unitsFrame,prepareFrame]
    rw [instEq]
    exact resumed_code hopInput op p f.inst beforeCode hn
  have beforeMem : hopInput.mems[p.memoryIndex]?=some p.memory := by simpa only [hopInput,before,initialAfter,paid,chargedStore] using hm
  have nextMem : nextStore.mems[p.memoryIndex]?=some (nextLayout p).memory := resumed_memory hopInput op p beforeMem
  have inspect := wp_inspect_success cfg (fuel+2) (op+rest) nextStore limits stack hf callers code (nextLayout p) post nextNative hopReady nextCode nextMem hd (c92.mono (by dsimp [op];omega)) inspectNext
  have hopNext : WP cfg (fuel+208) (.next (atCode (resumed hopInput op p) limits stack (inspectFrame hf stack.size code) callers WNear.Binary.AllocateSearch.inspect))
      (237*op+rest) post := by
    have fee : 236*cfg.regularOpCost+(op+rest)=237*op+rest := by dsimp [op];omega
    simpa only [finished,final,nextStore,fee,Nat.add_assoc,Nat.reduceAdd] using inspect
  have hop := wp_hop cfg (fuel+208) (237*op+rest) hopInput limits stack f callers code p post hn beforeCode fi.1 (fo.1.trans hw)
    (fo.2.1.trans hr) initialSize beforeMem hd (c21.mono (by dsimp [op];omega)) hopNext
  have enterNext : WP cfg (fuel+267) (.next (atCode (paid initial op 5) limits stack (inspectFrame f stack.size code) callers WNear.Binary.AllocateSearch.inspect))
      (308*op+rest) post := by
    have fee : 71*cfg.regularOpCost+(237*op+rest)=308*op+rest := by dsimp [op];omega
    simpa only [hopInput,before,initial,fee,Nat.add_assoc,Nat.reduceAdd] using hop
  have enter := wp_enter_search cfg (fuel+267) (308*op+rest) initial limits stack f callers code p post hn.headNonzero fi.1
    (c16.mono (by dsimp [op];omega)) enterNext
  have initialNext : WP cfg (fuel+278) (.next (atCode initial limits stack f callers
      (.block .empty WNear.Binary.AllocateSearch.outer::.local_get 5::code))) (313*op+rest) post := by
    have fee : 5*cfg.regularOpCost+(308*op+rest)=313*op+rest := by dsimp [op];omega
    simpa only [fee,Nat.add_assoc,Nat.reduceAdd] using enter
  have first := wp_initial cfg (fuel+278) (313*op+rest) s limits stack frame callers
    (.block .empty WNear.Binary.AllocateSearch.outer::.local_get 5::code) p post ha hr hcode.module hcode.memoryIndex hm hn.rootBound
    (hc.mono (by dsimp [op];omega)) initialNext
  have fee : 16*cfg.regularOpCost+(313*op+rest)=329*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [WNear.Binary.AllocateSearch.function_body]
  simpa only [fee,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using first
end
end WNear.Proofs.AllocateSkip
