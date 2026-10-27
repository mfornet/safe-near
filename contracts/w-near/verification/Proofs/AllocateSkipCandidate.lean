import Proofs.AllocateSkipPrepare
import Proofs.AllocateSkipUnits
import Proofs.AllocateSkipSize
import Proofs.AllocateSkipAdvance

/-! The complete actual first short candidate, ending at its root-update code. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode candidateAfter unitsFrom sizeFrom readI32
  WNear.Binary.AllocateSearch.inspect WNear.Binary.AllocateSearch.candidateLoop
  WNear.Binary.AllocateSearch.candidateInner WNear.Binary.AllocateSearch.candidateMiddle WNear.Binary.AllocateSearch.candidateOuter

def shortSkipped (height : Nat) : List Label :=
  [⟨0,height,WNear.Binary.AllocateSearch.candidateLoop.drop 1,none⟩,
   ⟨0,height,WNear.Binary.AllocateSearch.candidateInner.drop 1,some WNear.Binary.AllocateSearch.candidateLoop⟩,
   ⟨0,height,WNear.Binary.AllocateSearch.candidateMiddle.drop 1,none⟩]
def shortFrame (frame : CallFrame) (height : Nat) (code : Expr) := emptyBlockFrame (scanFrame frame height code) height []

theorem short_labels (frame : CallFrame) (height : Nat) (code : Expr) :
    inspectFrame frame height code=labelPrefixFrame (shortFrame frame height code) height (shortSkipped height) WNear.Binary.AllocateSkip.advance := by
  rw [←WNear.Binary.AllocateSkip.advance_eq]
  simp only [inspectFrame,shortFrame,shortSkipped,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,labelPrefixFrame,List.cons_append,List.nil_append]

private theorem units_modules (s : Store NearState) (op : Nat) : (unitsFrom s op).modules=s.modules := by
  have h := congrArg (fun t=>t.modules) (unitsFrom_resources s op)
  exact h
private theorem units_mems (s : Store NearState) (op : Nat) : (unitsFrom s op).mems=s.mems := by
  have h := congrArg (fun t=>t.mems) (unitsFrom_resources s op)
  exact h
private theorem units_funcs (s : Store NearState) (op : Nat) : (unitsFrom s op).funcs=s.funcs := by
  have h := congrArg (fun t=>t.funcs) (unitsFrom_resources s op)
  exact h
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih
 theorem wp_candidate_short (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : SearchCode s p frame.inst)
    (hh : frame.locals[1]?=some (.i32 (head p))) (hw : frame.locals[0]?=some (.i32 p.words))
    (hs : 14≤frame.locals.size) (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (60*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (candidateAfter s cfg.regularOpCost) limits stack
      (shortFrame (candidateFrame frame p) stack.size code) callers WNear.Binary.AllocateSkip.advance)) rest post) :
    WP cfg (fuel+45) (.next (atCode s limits stack (inspectFrame frame stack.size code) callers WNear.Binary.AllocateSearch.inspect))
      (60*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 10
  let scaled := unitsFrom prepared op
  let cf := candidateFrame frame p
  let co := shortFrame cf stack.size code
  let nf := inspectFrame cf stack.size code
  let discarded := .block .empty WNear.Binary.AllocateSearch.splitOuter::WNear.Binary.AllocateSearch.inspect.drop 19
  have c10 := paid_credits s op 10 (21*op+(29*op+rest)) (hc.mono (by dsimp [op];omega))
  have c31 := unitsFrom_credits prepared op (29*op+rest) c10
  have one : co.locals[1]?=some (.i32 (head p)) := by simp [co,cf,shortFrame,candidateFrame,unitsFrame,prepareFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,hh]
  have ten : co.locals[10]?=some (.i32 (p.words*4)) := by simp [co,cf,shortFrame,candidateFrame,unitsFrame,prepareFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,show 10<frame.locals.size by omega]
  have module : scaled.modules[co.inst]?=some p.mi := by
    rw [units_modules,modules_paid]
    simpa only [co,cf,shortFrame,candidateFrame,unitsFrame,prepareFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame] using hcode.module
  have memory : scaled.mems[p.memoryIndex]?=some p.memory := by
    rw [units_mems,mems_paid]
    exact hm
  have fn : scaled.funcs[p.sizeAddress]?=some (.wasm WNear.Binary.DeallocateList.sizeSignature co.inst WNear.Binary.DeallocateList.sizeFunction) := by
    rw [units_funcs,funcs_paid]
    simpa only [co,cf,shortFrame,candidateFrame,unitsFrame,prepareFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame] using hcode.sizeFunction
  have next : WP cfg fuel (.next (atCode (sizeFrom scaled op) limits stack co callers WNear.Binary.AllocateSkip.advance)) rest post := by
    simpa only [candidateAfter,scaled,prepared,co,cf,op] using hnext
  have size := wp_short_size cfg fuel rest scaled limits stack co callers (shortSkipped stack.size) WNear.Binary.AllocateSkip.advance discarded p post hn rfl
    one ten module hcode.memoryIndex memory hcode.sizeIndex fn hd c31 next
  have sizeNext : WP cfg (fuel+21) (.next (atCode scaled limits stack (candidateFrame (inspectFrame frame stack.size code) p) callers
      (WNear.Binary.AllocateSearch.candidateSize++discarded))) (29*op+rest) post := by
    rw [←short_labels] at size
    simpa only [co,cf,shortFrame,candidateFrame,unitsFrame,prepareFrame,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame] using size
  let pf := prepareFrame (inspectFrame frame stack.size code) p
  have codeP : Code prepared p pf.inst := by
    have instEq : pf.inst=frame.inst := by simp only [pf,prepareFrame,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame]
    rw [instEq]
    exact hcode.toCode.paid s op 10 p frame.inst
  have wP : pf.locals[0]?=some (.i32 p.words) := by
    simp [pf,prepareFrame,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame,hw]
  have ub := words_bound p hn
  have un : WP cfg (fuel+21) (.next (atCode (unitsFrom prepared op) limits stack (unitsFrame pf p) callers
      (WNear.Binary.AllocateSearch.candidateSize++discarded))) (29*op+rest) post := by
    simpa only [pf,candidateFrame,scaled] using sizeNext
  have units := wp_units cfg (fuel+21) (29*op+rest) prepared limits stack pf callers
    (WNear.Binary.AllocateSearch.candidateSize++discarded) p post ub codeP wP hd c10 un
  have unitNext : WP cfg (fuel+35) (.next (atCode prepared limits stack pf callers
      (WNear.Binary.AllocateSearch.candidateUnits++(WNear.Binary.AllocateSearch.candidateSize++discarded)))) (50*op+rest) post := by
    have fee : 21*cfg.regularOpCost+(29*op+rest)=50*op+rest := by dsimp [op];omega
    simpa only [fee,Nat.add_assoc,Nat.reduceAdd] using units
  let input := inspectFrame frame stack.size code
  have inputHead : input.locals[1]?=some (.i32 (head p)) := by
    simpa only [input,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame] using hh
  have inputSize : 10≤input.locals.size := by
    simpa only [input,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame] using (show 10≤frame.locals.size by omega)
  have inputModule : s.modules[input.inst]?=some p.mi := by
    simpa only [input,inspectFrame,scanFrame,outerFrame,emptyBlockFrame,emptyLoopFrame] using hcode.module
  have flag : readI32 p.memory ((head p).toNat+8) &&& 1=0 := by simpa only [AllocateSkip.next] using hn.candidateFlag
  have pn : WP cfg (fuel+35) (.next (atCode (paid s cfg.regularOpCost 10) limits stack (prepareFrame input p) callers
      (WNear.Binary.AllocateSearch.candidateUnits++WNear.Binary.AllocateSearch.candidateSize++discarded))) (50*op+rest) post := by
    simpa only [pf,input,prepared,op,List.append_assoc] using unitNext
  have prepRule := wp_prepare cfg (fuel+35) (50*op+rest) s limits stack input callers
    (WNear.Binary.AllocateSearch.candidateUnits++WNear.Binary.AllocateSearch.candidateSize++discarded) p post
  have first := prepRule hn.headBound flag inputHead inputSize inputModule hcode.memoryIndex hm
    (hc.mono (by dsimp [op];omega)) pn
  have fee : 10*cfg.regularOpCost+(50*op+rest)=60*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [WNear.Binary.AllocateSearch.inspect_eq]
  simpa only [input,discarded,fee,Nat.add_assoc,Nat.reduceAdd,List.append_assoc,List.cons_append,List.nil_append] using first
end
end WNear.Proofs.AllocateSkip
