import Proofs.StateDecodeRawOutput
import Proofs.StateDecodeRawCopyCall
import Proofs.StateDecodeRawChoiceSteps
import Proofs.StateDecodeRawStageCode

/-! f767's complete flag-zero choice executes the real769 chain, caches both
returned words, and explicitly returns through the actual output tail. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode checkedRaw flagCheckedRaw argumentsRaw allocatedRaw afterRaw

theorem wp_raw_choice (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (p : Layout) (a581 a236 : Nat) (post : Post) (hn : Native p) (hcode : Code s frame.inst p a581 a236)
    (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.globalRaw)
    (h0 : frame.locals[0]?=some (.i32 p.outRaw)) (h1 : frame.locals[1]?=some (.i32 1))
    (h2 : frame.locals[2]?=some (.i32 p.flag)) (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (h4 : frame.locals[4]?=some (.i32 p.size))
    (hs : 6≤frame.locals.size) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hd : callers.length+8<limits.maxCallDepth) (hc : s.host.gas.Credits (573*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (afterRaw cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+386) (.next (atCode (checkedRaw s cfg.regularOpCost p) limits base.toArray frame (caller::callers)
      (WNear.Binary.StateDecodeRaw.choice++rawFinish))) (475*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=emptyBlockFrame frame base.toArray.size rawFinish
  let rawCode:=WNear.Binary.StateDecodeRaw.rawArguments++WNear.Binary.StateDecodeRaw.rawCache
  let discarded:=WNear.Binary.StateDecodeRaw.zeroedArguments++WNear.Binary.StateDecodeRaw.zeroedCache++[.br 1]
  have output:=wp_raw_output cfg fuel rest s limits base frame caller callers p a581 a236 post hn hcode hm hg h0 h3 hs ha hh hc hnext
  have acode:=hcode.argumentsRaw s op frame.inst p a581 a236
  have call:=wp_copy_call cfg (fuel+21) (20*op+rest) (argumentsRaw s op p) limits base f (caller::callers)
    WNear.Binary.StateDecodeRaw.rawCache p a581 a236 post hn acode haRoot
    (argumentsRaw_memory s op p hm) (argumentsRaw_global s op p hg)
    (by simpa only[List.length_cons] using hd)
    ((argumentsRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[allocatedRaw,f,op] using output)
  have operands : (base++[Value.i32 (scratch p+16),.i32 p.size,.i32 1]).toArray=
      ((base.toArray.push (.i32 (scratch p+16))).push (.i32 p.size)).push (.i32 1) := by
    apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+376) (.next (atCode (argumentsRaw s op p) limits
      (((base.toArray.push (.i32 (scratch p+16))).push (.i32 p.size)).push (.i32 1)) f (caller::callers)
      (.call 769::WNear.Binary.StateDecodeRaw.rawCache))) (447*op+(20*op+rest)) post := by
    simpa only[operands,Nat.add_assoc,Nat.reduceAdd,op] using call
  have args:=wp_arguments769 cfg (fuel+376) (447*op+(20*op+rest)) (flagCheckedRaw s op p) limits base.toArray f (caller::callers)
    (.call 769::WNear.Binary.StateDecodeRaw.rawCache) (scratch p) p.size post h1 h4 h3
    ((flagCheckedRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[argumentsRaw,op] using cn)
  have args' : WP cfg (fuel+381) (.next (atCode (flagCheckedRaw s op p) limits base.toArray f (caller::callers) rawCode)) (472*op+rest) post:=by
    simpa only[arguments769Code,WNear.Binary.StateDecodeRaw.rawArguments,rawCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 5*cfg.regularOpCost+(447*op+(20*op+rest))=472*op+rest by dsimp[op];omega] using args
  have flag:=wp_raw_flag_zero cfg (fuel+381) (472*op+rest) (checkedRaw s op p) limits base.toArray f (caller::callers) rawCode discarded post
    (by simpa only[hn.flagZero,f,emptyBlockFrame] using h2)
    ((checkedRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[flagCheckedRaw,op] using args')
  have inner:=wp_block_empty cfg (fuel+384) (475*op+rest) (checkedRaw s op p) limits base.toArray f (caller::callers)
    (WNear.Binary.StateDecodeRaw.flagGuard++discarded) rawCode post
    ((checkedRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[show 3*cfg.regularOpCost+(472*op+rest)=475*op+rest by dsimp[op];omega] using flag)
  have outer:=wp_block_empty cfg (fuel+385) (475*op+rest) (checkedRaw s op p) limits base.toArray frame (caller::callers)
    (.block .empty (WNear.Binary.StateDecodeRaw.flagGuard++discarded)::rawCode) rawFinish post
    ((checkedRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2) inner
  simpa only[WNear.Binary.StateDecodeRaw.choice,rawCode,discarded,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using outer
end WNear.Proofs.StateDecodeRaw
