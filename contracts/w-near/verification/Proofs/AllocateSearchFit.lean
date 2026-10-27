import Proofs.AllocateSearchFitPrefix
import Proofs.AllocateSearchMinimum
import Proofs.AllocateSearchMutate
import Proofs.AllocateSearchPureFrame

/-! Complete actual successful innermost f580 split path, through real callees,
all heap writes, thirteen-label exit, and returned-pointer computation. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode readI32 arithmeticDone minimumDone Allocate.callbackAfter
  splitAfter linked initialized mutateAfter mutateInitialized minimumFrom Allocate.initializedStore controlAfter Allocate.committed

theorem wp_split_path (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code : Expr) (p : Layout) (post : Post)
    (hskip : skipped.length = 12) (hn : Native p) (hr : FitReady frame p)
    (hcode : Code s p frame.inst) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (176*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (splitAfter s cfg.regularOpCost p) limits stack (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel+155) (.next (atCode s limits stack
      (labelPrefixFrame frame stack.size skipped (WNear.Binary.Allocate.commit++code)) callers WNear.Binary.AllocateSearch.splitBody))
      (176*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let sf := splitFrame frame p
  let nested := labelPrefixFrame frame stack.size skipped (WNear.Binary.Allocate.commit++code)
  let fitted := labelPrefixFrame sf stack.size skipped (WNear.Binary.Allocate.commit++code)
  let discarded := WNear.Binary.AllocateSearch.splitBody.drop 98
  let tail := WNear.Binary.Allocate.initializeSplit++WNear.Binary.AllocateSearch.linkCode++discarded
  have v9 : 9 < frame.locals.size := by have := hr.localSize; omega
  have v2 : 2 < frame.locals.size := by have := hr.localSize; omega
  have sfHead : sf.locals[1]? = some (.i32 (head p)) := by
    simp [sf,splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,hr.headLocal]
  have sfHeader : sf.locals[9]? = some (.i32 (header p)) := by
    simp [sf,splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,v9,header]
  have sfLength : sf.locals[2]? = some (.i32 (Allocate.splitLength p.memory (head p) p.words)) := by
    simp [sf,splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,v2]
  have sfSize : 11 ≤ sf.locals.size := by
    simpa [sf,splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame] using (show 11 ≤ frame.locals.size by have := hr.localSize; omega)
  have cm := minimumDone_credits s op (75*op+rest) (hc.mono (by dsimp [op]; omega))
  have ca := arithmeticDone_credits s op (18*op+(75*op+rest)) (hc.mono (by dsimp [op]; omega))
  have codeM := minimumDone_code s op p frame.inst hcode
  have codeA := arithmeticDone_code s op p frame.inst hcode
  have memoryM : (minimumDone s op).mems[p.memoryIndex]? = some p.memory := by
    have eq := congrArg (fun t=>t.mems) (minimumDone_resources s op)
    simp only at eq
    rw [eq]
    exact hmem
  have mutateNext : WP cfg fuel (.next (atCode (mutateAfter (minimumDone s op) op p) limits stack (mutateFrame sf p) callers code)) rest post := by
    simpa only [splitAfter,linked,initialized,mutateAfter,mutateInitialized,mutateFrame,finalFrame,sf,op] using hnext
  have instSF : sf.inst = frame.inst := by
    simp only [sf,splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame]
  have moduleM : (minimumDone s op).modules[sf.inst]? = some p.mi := by
    rw [instSF]
    exact codeM.module
  have mutation := wp_mutate cfg fuel rest (minimumDone s op) limits stack sf callers skipped code discarded p post
    hskip hn sfHead sfHeader sfSize moduleM codeM.memoryIndex memoryM cm mutateNext
  have minNext : WP cfg (fuel+77) (.next (atCode (minimumFrom (arithmeticDone s op) op) limits stack fitted callers tail)) (75*op+rest) post := by
    have state : minimumFrom (arithmeticDone s op) op = minimumDone s op := by
      simp only [minimumFrom,minimumDone]
    rw [state]
    exact mutation
  have codeFitted : Code (arithmeticDone s op) p fitted.inst := by
    have instFitted : fitted.inst = frame.inst := by
      simp only [fitted,labelPrefixFrame,instSF]
    rw [instFitted]
    exact codeA
  have fittedLength : fitted.locals[2]? = some (.i32 (Allocate.splitLength p.memory (head p) p.words)) := by
    simpa only [fitted,labelPrefixFrame] using sfLength
  have minProof := wp_minimum_fit cfg (fuel+77) (75*op+rest) (arithmeticDone s op) limits stack fitted callers tail p post hn codeFitted fittedLength hd
    (ca.mono (by dsimp [op]; omega)) minNext
  have prefixNext : WP cfg (fuel+87) (.next (atCode (arithmeticDone s op) limits stack (splitFrame nested p) callers
      ([.local_get 2,.call 574]++tail))) (93*op+rest) post := by
    have cost : 18*cfg.regularOpCost+(75*op+rest)=93*op+rest := by dsimp [op]; omega
    rw [cost] at minProof
    simpa only [sf,nested,fitted,splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,labelPrefixFrame,atCode,
      Nat.add_assoc,Nat.reduceAdd] using minProof
  have ready : FitReady nested p := ⟨hr.words,hr.headLocal,hr.context,hr.vtable,hr.alignmentMask,hr.alignmentFlag,hr.dataBase,hr.byteCount,hr.localSize⟩
  have prefixProof := wp_fit_prefix cfg (fuel+87) (93*op+rest) s limits stack nested callers ([.local_get 2,.call 574]++tail) p post
    hn ready hcode hmem hd (hc.mono (by dsimp [op]; omega)) prefixNext
  have cost : 83*cfg.regularOpCost+(93*op+rest)=176*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at prefixProof
  rw [WNear.Binary.AllocateSearch.splitBody_eq]
  simpa only [nested,tail,discarded,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using prefixProof
end WNear.Proofs.AllocateSearch
