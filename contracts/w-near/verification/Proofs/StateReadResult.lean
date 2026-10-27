import Proofs.StateReadResultSteps

/-! Accepted deployed f498: guard, low eight bytes, then the updated high word.
No disjointness between source and destination is required. -/
namespace WNear.Proofs.StateReadResult
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64

 theorem lowStore_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (4 * op + rest)) :
    (lowStore s op index memory out source).host.gas.Credits rest :=
  paid_credits s op 4 rest hc

 theorem highStore_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (8 * op + rest)) :
    (highStore s op index memory out source).host.gas.Credits rest :=
  paid_credits s op 8 rest hc

/-- Actual f498 body under its accepted tag, including the free block entry.
The high-word bounds refer to the actual wrapping i32 addresses. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 source))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hwf : memory.wf) (hob : out.toNat + 8 ≤ memory.byteSize) (hsb : source.toNat + 8 ≤ memory.byteSize)
    (hoh : (out + 8).toNat + 4 ≤ memory.byteSize) (hsh : (source + 8).toNat + 4 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 0)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory out source) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 16) (.next (atCode s limits stack frame callers (WNear.Binary.StateRead.resultBody ++ code)))
      (15 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let guarded := paid s op 3
  let low := lowStore guarded op index memory out source
  have hg : guarded.host.gas.Credits (12 * op + rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have hl : low.host.gas.Credits (8 * op + rest) := lowStore_credits guarded op index _ memory out source (hg.mono (by omega))
  have hmg : guarded.modules[frame.inst]? = some mi := by simpa only [guarded,paid,chargedStore] using hm
  have hmemg : guarded.mems[index]? = some memory := by simpa only [guarded,paid,chargedStore] using hmem
  have hml : low.modules[frame.inst]? = some mi := by simpa only [low,lowStore,storeI64_modules,paid,chargedStore] using hmg
  have hmempaid : (paid guarded op 4).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmemg
  have hmeml : low.mems[index]? = some (lowMemory memory out source) :=
    storeI64_memory (paid guarded op 4) index out.toNat memory (readI64 memory source.toNat) hmempaid
  have hsize : (lowMemory memory out source).byteSize = memory.byteSize :=
    (writeI64_spec memory out.toNat (readI64 memory source.toNat) hwf hob).2.1
  have high := wp_high cfg fuel rest low limits stack frame callers code out source mi index (lowMemory memory out source) post
    ho hs hml hi hmeml (by rw [hsize]; exact hoh) (by rw [hsize]; exact hsh) hl hnext
  have middle := wp_low cfg (fuel + 8) (8 * op + rest) guarded limits stack frame callers
    (WNear.Binary.StateRead.resultHigh ++ code) out source mi index memory post ho hs hmg hi hmemg hob hsb
    (hg.mono (by omega)) high
  have middle' : WP cfg (fuel + 12) (.next (atCode guarded limits stack frame callers
      (WNear.Binary.StateRead.resultLow ++ WNear.Binary.StateRead.resultHigh ++ code))) (12 * op + rest) post := by
    simpa only [List.append_assoc, Nat.add_assoc, Nat.reduceAdd, op,
      show 4 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest) = 12 * cfg.regularOpCost + rest by omega] using middle
  have all := wp_guard cfg (fuel + 12) (12 * op + rest) s limits stack frame callers
    (WNear.Binary.StateRead.resultLow ++ WNear.Binary.StateRead.resultHigh ++ code) source mi index memory post hs hm hi hmem
    (by omega) htag (hc.mono (by dsimp [op]; omega)) middle'
  simpa only [WNear.Binary.StateRead.resultBody,List.append_eq,List.cons_append,List.nil_append,List.append_assoc,
    Nat.add_assoc,Nat.reduceAdd,op,
    show 3 * cfg.regularOpCost + (12 * cfg.regularOpCost + rest) = 15 * cfg.regularOpCost + rest by omega] using all

theorem after_credits (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (15 * op + rest)) :
    (after s op index memory out source).host.gas.Credits rest := by
  have hg := paid_credits s op 3 (12 * op + rest) (hc.mono (by omega))
  have hl := lowStore_credits (paid s op 3) op index (8 * op + rest) memory out source (hg.mono (by omega))
  exact highStore_credits _ op index rest _ out source hl

end WNear.Proofs.StateReadResult
