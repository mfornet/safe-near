import Proofs.AllocateVectorCache
import Proofs.AllocateFlaggedBranch

/-! The real two-label exit after690 discards the unselected688 allocation path. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_cache_branch (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (exit alternate : Expr) (scratch pointer size : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+16≤memory.byteSize) (hl : readI32 memory (scratch.toNat+8)=pointer)
    (hh : readI32 memory (scratch.toNat+12)=size)
    (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack
      {frame with locals:=(frame.locals.set! 5 (.i32 size)).set! 2 (.i32 pointer)} callers exit)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack
      (emptyBlockFrame (emptyBlockFrame frame stack.size exit) stack.size alternate) callers
      (WNear.Binary.AllocateVector.cache++[.br 1]))) (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := {frame with locals:=(frame.locals.set! 5 (.i32 size)).set! 2 (.i32 pointer)}
  let inner := emptyBlockFrame (emptyBlockFrame frame stack.size exit) stack.size alternate
  have br := AllocateFlagged.wp_br_label cfg fuel rest (paid s op 6) limits stack ff callers
    [{arity:=0,height:=stack.size,rest:=alternate,loop:=none}] exit [] post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) hnext
  have bn : WP cfg (fuel+1) (.next (atCode (paid s op 6) limits stack
      {inner with locals:=(inner.locals.set! 5 (.i32 size)).set! 2 (.i32 pointer)} callers [.br 1])) (op+rest) post := by
    simpa only [inner,ff,emptyBlockFrame,labelPrefixFrame,List.cons_append,List.nil_append,List.length_cons,List.length_nil] using br
  have ca := wp_cache cfg (fuel+1) (op+rest) s limits stack inner callers [.br 1] scratch pointer size mi index memory post
    h3 hm hi hmem hb hl hh (hc.mono (by dsimp [op];omega)) bn
  have ce : 6*cfg.regularOpCost+(op+rest)=7*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at ca
  simpa only [inner,Nat.add_assoc,Nat.reduceAdd] using ca
end WNear.Proofs.AllocateVector
