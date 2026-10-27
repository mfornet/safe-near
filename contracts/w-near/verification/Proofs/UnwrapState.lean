import Proofs.UnwrapStateCopyEntry
import Proofs.TotalSupply
import Proofs.LoadedCallees

/-! Actual accepted-state f155 execution through the proved byte-copy f951. -/
namespace WNear.Proofs.UnwrapState
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxHeartbeats 800000
set_option maxRecDepth 12000

/-- Actual nonzero state tag skips the absent-state panic tail. -/
theorem wp_tagCheck (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (source : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : source.toNat + 28 ≤ memory.byteSize)
    (htag : readI32 memory (source.toNat + 24) ≠ 0)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.UnwrapState.tagCheck ++ WNear.Binary.UnwrapState.panicTail))) (3 * cfg.regularOpCost + rest) post := by
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) s limits stack
    (emptyBlockFrame frame stack.size code) callers _ 1 (.i32 source) post hsource (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits stack
    (emptyBlockFrame frame stack.size code) callers _ {align := 2, offset := 24} source mi index memory post hm1 hindex hmem1
  · change source.toNat + 24 + 4 ≤ memory.byteSize; omega
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    WNear.Binary.UnwrapState.panicTail (readI32 memory (source.toNat + 24)) post htag
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- Actual arguments of the fixed forty-byte memcpy call. -/
theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (((stack.push (.i32 out)).push (.i32 source)).push (.i32 40)) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 1, .i32_const 40] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + (cfg.regularOpCost + rest)) by omega]
  apply wp_local_get cfg (fuel + 2) (cfg.regularOpCost + (cfg.regularOpCost + rest)) s limits stack frame callers _
    0 (.i32 out) post hout (hc.mono (by omega))
  apply wp_local_get cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits _ frame callers _ 1 (.i32 source) post hsource
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  apply wp_i32_const cfg fuel rest _ limits _ frame callers code 40 post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  · simpa only [paid] using hnext

def argumentStore (s : Store NearState) (op : Nat) : Store NearState := paid (paid s op 3) op 3

def finalStore (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) : Store NearState :=
  chargedStore (UnwrapStateCopyEntry.callAfter (argumentStore s op) op index out source memory 40) op

theorem finalStore_credits (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (rest : Nat) (hc : s.host.gas.Credits (744 * op + rest)) :
    (finalStore s op index out source memory).host.gas.Credits rest := by
  apply WNear.Proofs.StorePair.charged_credits
  apply UnwrapStateCopyEntry.callAfter_credits (argumentStore s op) op index out source memory 40 (op + rest) (by decide)
  apply paid_credits
  apply paid_credits s op 3
  exact hc.mono (by omega)

/-- Entire actual accepted f155 body, including its real forty-byte copy call
and subsequent drop. The absent-state panic branch is skipped by the tag. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out source : UInt32) (copyAddress : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hcopyAddress : mi.funcAddrs[951]? = some copyAddress)
    (hcopy : s.funcs[copyAddress]? = some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32) (hread : source.toNat + 40 ≤ memory.byteSize)
    (hwrite : out.toNat + 40 ≤ memory.byteSize) (htag : readI32 memory (source.toNat + 24) ≠ 0)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (744 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore s cfg.regularOpCost index out source memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 700) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.UnwrapState.body ++ code))) (744 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let args := argumentStore s op
  let copied := UnwrapStateCopyEntry.callAfter args op index out source memory 40
  let copyBudget := 737 * op + (op + rest)
  let argumentBudget := 3 * op + copyBudget
  have c3 : (paid s op 3).host.gas.Credits argumentBudget := paid_credits s op 3 argumentBudget (hc.mono (by dsimp [argumentBudget, copyBudget, op]; omega))
  have c6 : args.host.gas.Credits copyBudget := paid_credits (paid s op 3) op 3 copyBudget c3
  have ccopy : copied.host.gas.Credits (op + rest) :=
    UnwrapStateCopyEntry.callAfter_credits args op index out source memory 40 (op + rest) (by decide) c6
  have dropRule := wp_drop cfg fuel rest copied limits base.toArray frame callers code (.i32 out) post
  have dropped := dropRule ccopy hnext
  have stackResult : (base ++ [Value.i32 out]).toArray = base.toArray.push (.i32 out) := by
    apply Array.toList_inj.mp; simp
  have dropNext : WP cfg (fuel + 1) (.next (atCode copied limits (base ++ [Value.i32 out]).toArray frame callers (.drop :: code))) (op + rest) post := by
    simpa only [stackResult] using dropped
  have hm : args.modules[frame.inst]? = some mi := by simpa only [args, argumentStore, paid, chargedStore] using hmodule
  have hf : args.funcs[copyAddress]? = some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function) := by
    simpa only [args, argumentStore, paid, chargedStore] using hcopy
  have hmem : args.mems[index]? = some memory := by simpa only [args, argumentStore, paid, chargedStore] using hmemory
  have copyRule := UnwrapStateCopyEntry.wp_call cfg (fuel + 1) (op + rest) args limits base frame callers (.drop :: code)
    out source 40 copyAddress mi index memory post
  have copyEnv := copyRule hm hcopyAddress hf hindex hmem hwf
  have copyBounds := copyEnv (by decide) (by decide) hwidth hread hwrite hdepth
  have copyResult := copyBounds c6 dropNext
  have stackArguments : (base ++ [Value.i32 out, .i32 source, .i32 40]).toArray =
      ((base.toArray.push (.i32 out)).push (.i32 source)).push (.i32 40) := by
    apply Array.toList_inj.mp; simp
  have argumentsNext : WP cfg ((fuel + 1) + 692) (.next (atCode args limits
      (((base.toArray.push (.i32 out)).push (.i32 source)).push (.i32 40)) frame callers (.call 951 :: .drop :: code))) copyBudget post := by
    simpa only [show UInt32.ofNat 40 = (40 : UInt32) from rfl, stackArguments, Nat.reduceMul, Nat.reduceAdd, copyBudget, op] using copyResult
  have argumentRule := wp_arguments cfg ((fuel + 1) + 692) copyBudget (paid s op 3) limits base.toArray frame callers
    (.call 951 :: .drop :: code) out source post
  have argumentLocals := argumentRule hout hsource
  have arguments := argumentLocals c3 argumentsNext
  have tagRule := wp_tagCheck cfg (((fuel + 1) + 692) + 3) argumentBudget s limits base.toArray frame callers
    ([.local_get 0, .local_get 1, .i32_const 40, .call 951, .drop] ++ code) source mi index memory post
  have tagSource := tagRule hsource
  have tagEnv := tagSource hmodule hindex hmemory (by omega) htag
  have tagCredit : s.host.gas.Credits (3 * cfg.regularOpCost + argumentBudget) := hc.mono (by dsimp [argumentBudget, copyBudget, op]; omega)
  have checked := tagEnv tagCredit arguments
  have blockRule := wp_block_empty cfg ((((fuel + 1) + 692) + 3) + 3)
    (3 * cfg.regularOpCost + argumentBudget) s limits base.toArray frame callers
    (WNear.Binary.UnwrapState.tagCheck ++ WNear.Binary.UnwrapState.panicTail)
    ([.local_get 0, .local_get 1, .i32_const 40, .call 951, .drop] ++ code) post
  have whole := blockRule tagCredit checked
  have budget : 3 * cfg.regularOpCost + argumentBudget = 744 * cfg.regularOpCost + rest := by dsimp [argumentBudget, copyBudget, op]; omega
  rw [budget] at whole
  simpa only [WNear.Binary.UnwrapState.body, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using whole

end WNear.Proofs.UnwrapState
