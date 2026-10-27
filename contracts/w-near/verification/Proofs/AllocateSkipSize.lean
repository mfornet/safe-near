import Proofs.AllocateSkipNative
import NearVM.MeteredLabelRules

/-! The actual576 size and taken depth-three short-candidate branch. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode DeallocateListSize.after readI32
set_option maxRecDepth 16384

 theorem wp_short_size (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (p : Layout) (post : Post)
    (hn : Native p) (hskip : skipped.length=3)
    (hh : frame.locals[1]?=some (.i32 (head p))) (hb : frame.locals[10]?=some (.i32 (p.words*4)))
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.memAddrs[0]?=some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hfi : p.mi.funcAddrs[576]?=some p.sizeAddress)
    (hf : s.funcs[p.sizeAddress]?=some (.wasm WNear.Binary.DeallocateList.sizeSignature frame.inst WNear.Binary.DeallocateList.sizeFunction))
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (29*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (sizeFrom s cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel+21) (.next (atCode s limits stack (labelPrefixFrame frame stack.size skipped code) callers
      (WNear.Binary.AllocateSearch.candidateSize++discarded))) (29*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let nf := labelPrefixFrame frame stack.size skipped code
  let sized := DeallocateListSize.after (paid s op 1) op
  have c1 := paid_credits s op 1 (25*op+(3*op+rest)) (hc.mono (by dsimp [op];omega))
  have c26 := DeallocateListSize.after_credits (paid s op 1) op (3*op+rest) c1
  have bn : WP cfg fuel (.next (atCode (chargedStore (paid sized op 2) cfg.regularOpCost) limits stack frame callers code)) rest post := by
    simpa only [sizeFrom,sized,op,paid] using hnext
  have branch := wp_br_if_label_nonzero cfg fuel rest (paid sized op 2) limits stack frame callers skipped code discarded 1 post
    (by decide) (paid_credits sized op 2 _ (c26.mono (by dsimp [op];omega))) bn
  have rn : WP cfg (fuel+1) (.next (atCode (chargedStore (paid sized op 1) cfg.regularOpCost) limits
      (stack.push (.i32 (Numeric.bool (Numeric.irelop32 .lt_u (DeallocateListSize.size p.memory (head p)) (p.words*4)))))
      nf callers (.br_if 3::discarded))) (op+rest) post := by
    simpa only [first_short p hn,Numeric.bool,ite_true,hskip,nf,paid,op] using branch
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid sized op 1) limits stack nf callers (.br_if 3::discarded)
    .lt_u (DeallocateListSize.size p.memory (head p)) (p.words*4) post (paid_credits sized op 1 _ (c26.mono (by dsimp [op];omega))) rn
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) sized limits (stack.push (.i32 (DeallocateListSize.size p.memory (head p))))
    nf callers (.i32_relop .lt_u::.br_if 3::discarded) 10 (.i32 (p.words*4)) post hb (c26.mono (by dsimp [op];omega)) rel
  have arr : (stack.toList++[Value.i32 (DeallocateListSize.size p.memory (head p))]).toArray=stack.push (.i32 (DeallocateListSize.size p.memory (head p))) := by apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+3) (.next (atCode sized limits (stack.toList++[Value.i32 (DeallocateListSize.size p.memory (head p))]).toArray nf callers
      (.local_get 10::.i32_relop .lt_u::.br_if 3::discarded))) (3*op+rest) post := by
    have ce : cfg.regularOpCost+(op+(op+rest))=3*op+rest := by dsimp [op];omega
    simpa only [arr,ce] using get
  have hm1 : (paid s op 1).modules[nf.inst]?=some p.mi := hm
  have mem1 : (paid s op 1).mems[p.memoryIndex]?=some p.memory := hmem
  have fn1 : (paid s op 1).funcs[p.sizeAddress]?=some (.wasm WNear.Binary.DeallocateList.sizeSignature nf.inst WNear.Binary.DeallocateList.sizeFunction) := hf
  have call := DeallocateListSize.wp_call cfg (fuel+3) (3*op+rest) (paid s op 1) limits stack.toList nf callers
    (.local_get 10::.i32_relop .lt_u::.br_if 3::discarded) (head p) p.mi p.sizeAddress p.memoryIndex p.memory post
    hm1 hfi fn1 hi mem1 (by have:=hn.headBound;omega) hn.firstNormal hd c1 cn
  have arg : (stack.toList++[Value.i32 (head p)]).toArray=stack.push (.i32 (head p)) := by apply Array.toList_inj.mp;simp
  have gn : WP cfg (fuel+20) (.next (atCode (paid s op 1) limits (stack.push (.i32 (head p))) nf callers
      (.call 576::.local_get 10::.i32_relop .lt_u::.br_if 3::discarded))) (28*op+rest) post := by
    have ce : 25*cfg.regularOpCost+(3*op+rest)=28*op+rest := by dsimp [op];omega
    simpa only [arg,ce,Nat.add_assoc,Nat.reduceAdd] using call
  have first := wp_local_get cfg (fuel+20) (28*op+rest) s limits stack nf callers _ 1 (.i32 (head p)) post hh
    (hc.mono (by dsimp [op];omega)) gn
  have ce : cfg.regularOpCost+(28*op+rest)=29*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateSearch.candidateSize,List.cons_append,List.nil_append,ce] using first
end WNear.Proofs.AllocateSkip
