import Proofs.AllocateVectorPhases

/-! The result words are read and cached before any caller output write. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

theorem wp_cache (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch pointer size : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+16≤memory.byteSize) (hl : readI32 memory (scratch.toNat+8)=pointer)
    (hh : readI32 memory (scratch.toNat+12)=size)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack
      {frame with locals:=(frame.locals.set! 5 (.i32 size)).set! 2 (.i32 pointer)} callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVector.cache++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let ff := loadedFrame frame 5 size
  have h3f : ff.locals[3]?=some (.i32 scratch) := by simp [ff,loadedFrame,h3]
  have mm : (paid s op 3).modules[ff.inst]?=some mi := hm
  have me : (paid s op 3).mems[index]?=some memory := hmem
  have ln : WP cfg fuel (.next (atCode (paid (paid s op 3) op 3) limits stack
      (loadedFrame ff 2 (readI32 memory (scratch.toNat+8))) callers code)) rest post := by
    simpa only [loadedFrame,ff,hl,paid,op] using hnext
  have low := wp_load_local cfg fuel rest (paid s op 3) limits stack ff callers code 3 2 8 scratch mi index memory post h3f mm hi me
    (by omega) (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) ln
  have hn : WP cfg (fuel+3) (.next (atCode (paid s op 3) limits stack
      (loadedFrame frame 5 (readI32 memory (scratch.toNat+12))) callers
      ([.local_get 3,.load .i32 none {align:=2,offset:=8},.local_set 2]++code))) (3*op+rest) post := by
    simpa only [hh,ff,op] using low
  have high := wp_load_local cfg (fuel+3) (3*op+rest) s limits stack frame callers
    ([.local_get 3,.load .i32 none {align:=2,offset:=8},.local_set 2]++code) 3 5 12 scratch mi index memory post h3 hm hi hmem
    (by omega) (hc.mono (by dsimp [op];omega)) hn
  have ce : 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at high
  simpa only [WNear.Binary.AllocateVector.cache,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using high
end WNear.Proofs.AllocateVector
