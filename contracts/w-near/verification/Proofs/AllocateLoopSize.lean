import Binary.AllocateLoop
import Proofs.AllocateSearchPhases
import Proofs.DeallocateListSize

/-! Actual576 and the candidate-capacity branch, accepted from the original free interval. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode DeallocateListSize.after

def sizeFrom (s : Store NearState) (op : Nat) := paid (DeallocateListSize.after (paid s op 1) op) op 3

theorem candidate_fits (p : Layout) (hn : Native p) :
    Numeric.irelop32 .lt_u (DeallocateListSize.size p.memory (head p)) (p.words*4) = false := by
  have room := hn.split.room
  have endLt := UInt32.toNat_lt (Allocate.endWord p.memory (head p))
  have normal : (head p).toNat+8≤(DeallocateListSize.endWord p.memory (head p)).toNat := by
    change (head p).toNat+8≤(Allocate.endWord p.memory (head p)).toNat
    omega
  have sizeNat := DeallocateListSize.size_nat p.memory (head p) normal
  have count : (p.words*4).toNat=p.words.toNat*4 := by
    rw [UInt32.toNat_mul]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    omega
  change decide (DeallocateListSize.size p.memory (head p) < p.words*4) = false
  simp only [decide_eq_false_iff_not,UInt32.lt_iff_toNat_lt,sizeNat,count]
  change ¬ (Allocate.endWord p.memory (head p)).toNat-(head p).toNat-8<p.words.toNat*4
  omega

theorem wp_candidate_size (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p)
    (hh : frame.locals[1]? = some (.i32 (head p))) (hb : frame.locals[10]? = some (.i32 (p.words*4)))
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hfi : p.mi.funcAddrs[576]? = some p.sizeAddress)
    (hf : s.funcs[p.sizeAddress]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction))
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (29*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (sizeFrom s cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel+21) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateSearch.candidateSize++code)))
      (29*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let sized := DeallocateListSize.after (paid s op 1) op
  have room := hn.split.room
  have bounds := intervals p hn
  have normal : (head p).toNat+8≤(DeallocateListSize.endWord p.memory (head p)).toNat := by
    change (head p).toNat+8≤(Allocate.endWord p.memory (head p)).toNat
    omega
  have c1 := paid_credits s op 1 (25*op+(3*op+rest)) (hc.mono (by dsimp [op]; omega))
  have c26 : sized.host.gas.Credits (3*op+rest) := DeallocateListSize.after_credits (paid s op 1) op (3*op+rest) c1
  have branchNext : WP cfg fuel (.next (atCode (chargedStore (paid sized op 2) cfg.regularOpCost) limits stack frame callers code)) rest post := by
    simpa only [sizeFrom,sized,op,paid] using hnext
  have branch := wp_br_if_zero cfg fuel rest (paid sized op 2) limits stack frame callers code 3 post
    (paid_credits sized op 2 _ (c26.mono (by dsimp [op]; omega))) branchNext
  have relNext : WP cfg (fuel+1) (.next (atCode (chargedStore (paid sized op 1) cfg.regularOpCost) limits
      (stack.push (.i32 (Numeric.bool (Numeric.irelop32 .lt_u (DeallocateListSize.size p.memory (head p)) (p.words*4)))))
      frame callers (.br_if 3::code))) (op+rest) post := by
    simpa only [candidate_fits p hn,Numeric.bool,Bool.false_eq_true,ite_false,paid,op] using branch
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid sized op 1) limits stack frame callers (.br_if 3::code)
    .lt_u (DeallocateListSize.size p.memory (head p)) (p.words*4) post
    (paid_credits sized op 1 _ (c26.mono (by dsimp [op]; omega))) relNext
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) sized limits (stack.push (.i32 (DeallocateListSize.size p.memory (head p))))
    frame callers (.i32_relop .lt_u::.br_if 3::code) 10 (.i32 (p.words*4)) post hb (c26.mono (by dsimp [op]; omega)) rel
  have arr : (stack.toList++[Value.i32 (DeallocateListSize.size p.memory (head p))]).toArray = stack.push (.i32 (DeallocateListSize.size p.memory (head p))) := by apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel+3) (.next (atCode sized limits (stack.toList++[Value.i32 (DeallocateListSize.size p.memory (head p))]).toArray
      frame callers (.local_get 10::.i32_relop .lt_u::.br_if 3::code))) (3*op+rest) post := by
    have cost : cfg.regularOpCost+(op+(op+rest))=3*op+rest := by dsimp [op]; omega
    rw [cost] at get
    simpa only [arr] using get
  have hm1 : (paid s op 1).modules[frame.inst]? = some p.mi := by simpa only [paid,chargedStore] using hm
  have mem1 : (paid s op 1).mems[p.memoryIndex]? = some p.memory := by simpa only [paid,chargedStore] using hmem
  have f1 : (paid s op 1).funcs[p.sizeAddress]? = some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction) := by simpa only [paid,chargedStore] using hf
  have call := DeallocateListSize.wp_call cfg (fuel+3) (3*op+rest) (paid s op 1) limits stack.toList frame callers
    (.local_get 10::.i32_relop .lt_u::.br_if 3::code) (head p) p.mi p.sizeAddress p.memoryIndex p.memory post hm1 hfi f1 hi mem1
    (by omega) normal hd c1 callNext
  have arg : (stack.toList++[Value.i32 (head p)]).toArray = stack.push (.i32 (head p)) := by apply Array.toList_inj.mp; simp
  have getNext : WP cfg (fuel+20) (.next (atCode (paid s op 1) limits (stack.push (.i32 (head p))) frame callers
      (.call 576::.local_get 10::.i32_relop .lt_u::.br_if 3::code))) (28*op+rest) post := by
    have cost : 25*cfg.regularOpCost+(3*op+rest)=28*op+rest := by dsimp [op]; omega
    rw [cost] at call
    simpa only [arg,Nat.add_assoc,Nat.reduceAdd] using call
  have result := wp_local_get cfg (fuel+20) (28*op+rest) s limits stack frame callers _ 1 (.i32 (head p)) post hh
    (hc.mono (by dsimp [op]; omega)) getNext
  have cost : cfg.regularOpCost+(28*op+rest)=29*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [WNear.Binary.AllocateSearch.candidateSize,List.append_eq,List.cons_append,List.nil_append] using result
end WNear.Proofs.AllocateSearch
