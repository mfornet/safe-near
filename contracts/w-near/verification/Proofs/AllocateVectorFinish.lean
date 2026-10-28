import Proofs.AllocateVectorTail
import Proofs.AllocateVectorControl

/-! Successful pointer guard, output and explicitreturn, independent of allocation internals. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode finished

theorem wp_finish (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index globalIndex : Nat) (global : GlobalInst)
    (memory : Memory) (out pointer size scratch : UInt32) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h2 : frame.locals[2]?=some (.i32 pointer))
    (h5 : frame.locals[5]?=some (.i32 size)) (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hgi : mi.globalAddrs[0]?=some globalIndex)
    (hg : s.globals[globalIndex]?=some global) (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (hn : pointer≠0) (ha : frame.arity=0) (hh : frame.height=base.length)
    (hc : s.host.gas.Credits (14*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (finished (paid s cfg.regularOpCost 3) cfg.regularOpCost index globalIndex memory out pointer size scratch)
      limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+14) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateVector.nonzero++WNear.Binary.AllocateVector.record++WNear.Binary.AllocateVector.restore++(.return::code))))
      (14*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have tail := wp_tail cfg fuel rest (paid s op 3) limits base frame caller callers code mi index globalIndex global memory out pointer size scratch post
    h0 h2 h5 h3 hm hi hmem hgi hg hw hb ha hh
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) hnext
  have guard := wp_nonzero cfg (fuel+11) (11*op+rest) s limits base.toArray frame (caller::callers)
    (WNear.Binary.AllocateVector.record++WNear.Binary.AllocateVector.restore++(.return::code)) 2 1 pointer post h2 hn
    (hc.mono (by dsimp [op];omega)) tail
  have ce : 3*cfg.regularOpCost+(11*op+rest)=14*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at guard
  simpa only [WNear.Binary.AllocateVector.nonzero,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using guard
end WNear.Proofs.AllocateVector
