import Proofs.AllocateLoopPrepare
import Proofs.AllocateLoopUnits
import Proofs.AllocateLoopSize
import Proofs.ValueReturnBorrow

/-! Complete real candidate preparation,572 scaling,576 size, and fit branch. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode unitsFrom sizeFrom

def candidateAfter (s : Store NearState) (op : Nat) := sizeFrom (unitsFrom (paid s op 10) op) op
def candidateFrame (frame : CallFrame) (p : Layout) := unitsFrame (prepareFrame frame p) p

structure SearchCode (s : Store NearState) (p : Layout) (inst : Nat) : Prop extends Code s p inst where
  sizeIndex : p.mi.funcAddrs[576]? = some p.sizeAddress
  sizeFunction : s.funcs[p.sizeAddress]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature inst WNear.Binary.DeallocateList.sizeFunction)

theorem unitsFrom_resources (s : Store NearState) (op : Nat) : {unitsFrom s op with host:=s.host}=s := by
  simp only [unitsFrom,AllocateUnits.unitsAfter,AllocateUnits.entered9,paid,chargedStore]
theorem sizeFrom_resources (s : Store NearState) (op : Nat) : {sizeFrom s op with host:=s.host}=s := by
  simp only [sizeFrom,DeallocateListSize.after,DeallocateListSize.entered,paid,chargedStore]
theorem unitsFrom_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (21*op+rest)) :
    (unitsFrom s op).host.gas.Credits rest := by
  unfold unitsFrom
  apply paid_credits (AllocateUnits.unitsAfter (paid s op 1) op) op 1 rest
  exact AllocateUnits.unitsAfter_credits (paid s op 1) op _ (paid_credits s op 1 _ (hc.mono (by omega)))
theorem sizeFrom_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (29*op+rest)) :
    (sizeFrom s op).host.gas.Credits rest := by
  unfold sizeFrom
  apply paid_credits (DeallocateListSize.after (paid s op 1) op) op 3 rest
  exact DeallocateListSize.after_credits (paid s op 1) op _ (paid_credits s op 1 _ (hc.mono (by omega)))

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
end WNear.Proofs.AllocateSearch
