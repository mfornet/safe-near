import Proofs.AllocateFlaggedPrepare
import Proofs.AllocateFlaggedUnits
import Proofs.AllocateFlaggedSize

/-! Flag-aware composition of the actual572/576 candidate checks. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode unitsFrom sizeFrom

theorem wp_candidate (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : SearchCode s p frame.inst)
    (hh : frame.locals[1]? = some (.i32 (head p))) (hw : frame.locals[0]? = some (.i32 p.words))
    (hs : 14 ≤ frame.locals.size) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (60*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (candidateAfter s cfg.regularOpCost) limits stack (candidateFrame frame p) callers code)) rest post) :
    WP cfg (fuel+45) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateSearch.candidatePrepare++WNear.Binary.AllocateSearch.candidateUnits++WNear.Binary.AllocateSearch.candidateSize++code)))
      (60*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 10
  let scaled := unitsFrom prepared op
  let pf := prepareFrame frame p
  let cf := candidateFrame frame p
  have cr := unitsFrom_resources prepared op
  have c10 := paid_credits s op 10 (21*op+(29*op+rest)) (hc.mono (by dsimp [op]; omega))
  have c31 := unitsFrom_credits prepared op (29*op+rest) c10
  have h1 : cf.locals[1]? = some (.i32 (head p)) := by simp [cf,candidateFrame,unitsFrame,prepareFrame,hh]
  have v10 : 10 < frame.locals.size := by omega
  have h10 : cf.locals[10]? = some (.i32 (p.words*4)) := by simp [cf,candidateFrame,unitsFrame,prepareFrame,v10]
  have mi : scaled.modules[cf.inst]? = some p.mi := by
    have inst : cf.inst=frame.inst := rfl
    rw [inst,show scaled.modules=prepared.modules from congrArg (fun t=>t.modules) cr]
    simpa only [prepared,paid,chargedStore] using hcode.module
  have mem : scaled.mems[p.memoryIndex]? = some p.memory := by
    rw [show scaled.mems=prepared.mems from congrArg (fun t=>t.mems) cr]
    simpa only [prepared,paid,chargedStore] using hmem
  have sf : scaled.funcs[p.sizeAddress]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature cf.inst WNear.Binary.DeallocateList.sizeFunction) := by
    have inst : cf.inst=frame.inst := rfl
    rw [inst,show scaled.funcs=prepared.funcs from congrArg (fun t=>t.funcs) cr]
    simpa only [prepared,paid,chargedStore] using hcode.sizeFunction
  have sn : WP cfg fuel (.next (atCode (sizeFrom scaled op) limits stack cf callers code)) rest post := by
    simpa only [candidateAfter,scaled,prepared,cf,op] using hnext
  have size := wp_candidate_size cfg fuel rest scaled limits stack cf callers code p post hn h1 h10 mi hcode.memoryIndex mem
    hcode.sizeIndex sf hd c31 sn
  have un : WP cfg (fuel+21) (.next (atCode (unitsFrom prepared op) limits stack (unitsFrame pf p) callers
      (WNear.Binary.AllocateSearch.candidateSize++code))) (29*op+rest) post := size
  have cp := hcode.toCode.paid s op 10 p frame.inst
  have codeP : Code prepared p pf.inst := by
    have inst : pf.inst=frame.inst := rfl
    rw [inst]; exact cp
  have wP : pf.locals[0]? = some (.i32 p.words) := by simp [pf,prepareFrame,hw]
  have units := wp_candidate_units cfg (fuel+21) (29*op+rest) prepared limits stack pf callers
    (WNear.Binary.AllocateSearch.candidateSize++code) p post hn codeP wP hd c10 un
  have pn : WP cfg (fuel+35) (.next (atCode prepared limits stack pf callers
      (WNear.Binary.AllocateSearch.candidateUnits++WNear.Binary.AllocateSearch.candidateSize++code))) (50*op+rest) post := by
    have cost : 21*cfg.regularOpCost+(29*op+rest)=50*op+rest := by dsimp [op]; omega
    rw [cost] at units
    simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using units
  have result := wp_candidate_prepare cfg (fuel+35) (50*op+rest) s limits stack frame callers
    (WNear.Binary.AllocateSearch.candidateUnits++WNear.Binary.AllocateSearch.candidateSize++code) p post hn hh (by omega)
    hcode.module hcode.memoryIndex hmem (hc.mono (by dsimp [op]; omega)) pn
  have cost : 10*cfg.regularOpCost+(50*op+rest)=60*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using result
end WNear.Proofs.AllocateFlagged
