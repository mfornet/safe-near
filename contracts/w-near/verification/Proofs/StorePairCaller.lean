import Proofs.StorePairCallerState
import Proofs.StorePair
import Binary.StorePairCaller
import NearVM.MeteredScalarRules
import NearVM.MeteredWasmCall
import Proofs.StorePairReadback
import Proofs.StorePairAddresses

/-! Alias-aware memory and actual-body composition for deployed f414. -/
namespace WNear.Proofs.StorePairCaller
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePair
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- The actual five-instruction prologue reserves its stack slot. Arbitrary
operand prefixes, enclosing labels and caller frames are preserved. -/
theorem wp_prologue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 5) index (.i32 (sp - 16))) limits stack
      {frame with locals := frame.locals.set! 2 (.i32 (sp - 16))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 2, .global_set 0] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have h1 := paid_credits s cfg.regularOpCost 1 (4 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h2 := paid_credits s cfg.regularOpCost 2 (3 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h3 := paid_credits s cfg.regularOpCost 3 (2 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h4 := paid_credits s cfg.regularOpCost 4 (cfg.regularOpCost + rest) (hc.mono (by omega))
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg4 : (paid s cfg.regularOpCost 4).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  have hget := wp_global_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.i32_const 16, .i32_binop .sub, .local_tee 2, .global_set 0] ++ code)
    0 index mi global post hmodule hindex hglobal h0
  rw [hsp] at hget
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply hget
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 16 post
    (by simpa only [paid, show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega] using h1)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_sub cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits stack frame callers _ sp 16 post
    (by simpa only [paid, show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega] using h2)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ 2 (.i32 (sp - 16)) post
    (by simpa only [paid, show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega] using h3)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 4) limits stack {frame with locals := frame.locals.set! 2 (.i32 (sp - 16))} callers code 0 index mi (.i32 (sp - 16)) global post
    hm4 hindex hg4
  · simpa only [paid] using h4
  · simpa only [paid] using hnext

/-- Both source words are read before the nested helper can modify scratch.
The two input and one scratch addresses need no disjointness. -/
theorem wp_load_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (scratch source : UInt32) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 scratch))
    (hsource : frame.locals[1]? = some (.i32 source))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hplus : (source + 8).toNat = source.toNat + 8)
    (hbound : source.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 scratch)).push (.i64 (readI64 memory source.toNat))).push
        (.i64 (readI64 memory (source.toNat + 8)))) frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      ([.local_get 2, .local_get 1, .load .i64 none {align := 3, offset := 0},
        .local_get 1, .i32_const 8, .i32_binop .add,
        .load .i64 none {align := 3, offset := 0}] ++ code)))
      (7 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm6 : (paid s cfg.regularOpCost 6).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem6 : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) (6 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 scratch) post hscratch
    (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) (5 * cfg.regularOpCost + rest) _ limits _ frame callers _ 1 (.i32 source) post hsource
  · apply paid_credits s cfg.regularOpCost 1
    exact hc.mono (by omega)
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 3, offset := 0} source mi index memory post hm2 hindex hmem2 (by change source.toNat + 0 + 8 ≤ memory.byteSize; omega)
  · apply paid_credits s cfg.regularOpCost 2
    exact hc.mono (by omega)
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 1 (.i32 source) post hsource
  · apply paid_credits s cfg.regularOpCost 3
    exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 8 post
  · apply paid_credits s cfg.regularOpCost 4
    exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits _ frame callers _ source 8 post
  · apply paid_credits s cfg.regularOpCost 5
    exact hc.mono (by omega)
  apply wp_i64_load cfg fuel rest (paid s cfg.regularOpCost 6) limits _ frame callers code {align := 3, offset := 0} (source + 8) mi index memory post
    hm6 hindex hmem6 (by change (source + 8).toNat + 0 + 8 ≤ memory.byteSize; rw [hplus]; omega)
  · apply paid_credits s cfg.regularOpCost 6
    exact hc.mono (by omega)
  · simpa only [hplus, Nat.add_zero, paid] using hnext

/-- The final four instructions restore the saved stack pointer without
altering locals, operand prefixes or enclosing callers. -/
theorem wp_restore (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (scratch : UInt32) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 16))) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg3 : (paid s cfg.regularOpCost 3).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 scratch) post hscratch
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 16 post
  · apply paid_credits s cfg.regularOpCost 1
    exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ scratch 16 post
  · apply paid_credits s cfg.regularOpCost 2
    exact hc.mono (by omega)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 0 index mi (.i32 (scratch + 16)) global post
    hm3 hindex hg3
  · apply paid_credits s cfg.regularOpCost 3
    exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- The actual nested call to deployed f566 returns normally to any saved
caller, with its operand prefix, labels, locals and following code restored. -/
theorem wp_nested_helper (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address : Nat) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (scratch : UInt32) (lo hi : UInt64) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[566]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.StorePair.signature frame.inst WNear.Binary.StorePair.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hbound : scratch.toNat + 16 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (18 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (pairStore (chargedStore (chargedStore s cfg.regularOpCost) (11 * cfg.regularOpCost))
        cfg.regularOpCost index scratch.toNat memory lo hi)
      limits stack.toArray frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits (stack ++ [Value.i32 scratch, Value.i64 lo, Value.i64 hi]).toArray
      frame callers (.call 566 :: code))) (18 * cfg.regularOpCost + rest) post := by
  let entered := chargedStore (chargedStore s cfg.regularOpCost) (11 * cfg.regularOpCost)
  let leaf : CallFrame := { locals := #[.i32 scratch, .i64 lo, .i64 hi], inst := frame.inst, arity := 0, height := stack.length, labels := [], code := [] }
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (11 * cfg.regularOpCost + (6 * cfg.regularOpCost + rest))) :=
    hc.mono (by omega)
  have h1 := charged_credits s cfg.regularOpCost _ h0
  have h2 := charged_credits (chargedStore s cfg.regularOpCost) (11 * cfg.regularOpCost) _ h1
  have h3 := storeWord_credits entered cfg.regularOpCost index (scratch.toNat + 8)
    (3 * cfg.regularOpCost + rest) memory hi (h2.mono (by omega))
  have h4 := storeWord_credits (storeWord entered cfg.regularOpCost index (scratch.toNat + 8) memory hi)
    cfg.regularOpCost index scratch.toNat rest (writeI64 memory (scratch.toNat + 8) hi) lo h3
  have hmEntered : entered.modules[frame.inst]? = some mi := by simpa only [entered, chargedStore] using hmodule
  have hmemEntered : entered.mems[index]? = some memory := by simpa only [entered, chargedStore] using hmemory
  have hfinalCredits : (pairStore entered cfg.regularOpCost index scratch.toNat memory lo hi).host.gas.Credits rest := by
    simpa only [pairStore] using h4
  have hleave := wp_leave_wasm cfg fuel rest
    (pairStore entered cfg.regularOpCost index scratch.toNat memory lo hi)
    limits stack [] leaf {frame with code} callers post rfl rfl rfl hfinalCredits
    (by simpa only [entered, atCode, List.append_nil] using hnext)
  have hbody := WNear.Proofs.StorePair.wp_body cfg (fuel + 1) rest entered limits stack.toArray leaf
    ({frame with code} :: callers) [] scratch lo hi mi index memory post rfl rfl rfl
    hmEntered hindex hmemEntered hwf hbound h2
    (by simpa only [List.append_nil] using hleave)
  have hcall := wp_call_wasm cfg (fuel + 7) (6 * cfg.regularOpCost + rest) s limits stack
    [.i32 scratch, .i64 lo, .i64 hi] frame callers code 566 address mi WNear.Binary.StorePair.signature
    frame.inst WNear.Binary.StorePair.function post hmodule haddress hfunction rfl hdepth
  have hactivation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.StorePair.function [.i32 scratch, .i64 lo, .i64 hi]) = 11 * cfg.regularOpCost := by
    exact WNear.Binary.StorePair.activation_cost _ _ _ _
  rw [hactivation] at hcall
  have hconfig : atCode entered limits stack.toArray leaf ({frame with code} :: callers) WNear.Proofs.StorePair.body =
      wasmCallee entered limits stack frame callers code WNear.Binary.StorePair.signature frame.inst
        WNear.Binary.StorePair.function [Value.i32 scratch, Value.i64 lo, Value.i64 hi] := by
    rfl
  have hcallee : WP cfg (fuel + 7)
      (.next (wasmCallee entered limits stack frame callers code WNear.Binary.StorePair.signature
        frame.inst WNear.Binary.StorePair.function [Value.i32 scratch, Value.i64 lo, Value.i64 hi]))
      (6 * cfg.regularOpCost + rest) post := by
    rw [← hconfig]
    simpa only [List.append_nil] using hbody
  have h := hcall h0 hcallee
  simpa only [show cfg.regularOpCost + (11 * cfg.regularOpCost + (6 * cfg.regularOpCost + rest)) =
    18 * cfg.regularOpCost + rest by omega] using h

/-- Actual output phase: read both scratch words before writing either output
word. Source, scratch and output regions may alias. -/
theorem wp_output (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (memory : Memory)
    (scratch out : UInt32) (lo hi : UInt64) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 scratch)) (hout : frame.locals[0]? = some (.i32 out))
    (hsize : 3 < frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hplus : (scratch + 8).toNat = scratch.toNat + 8)
    (hscratchBound : scratch.toNat + 16 ≤ memory.byteSize) (houtBound : out.toNat + 16 ≤ memory.byteSize)
    (hlow : readI64 memory scratch.toNat = lo) (hhigh : readI64 memory (scratch.toNat + 8) = hi)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeWord (storeI64 (paid s cfg.regularOpCost 9) index (out.toNat + 8) memory hi)
        cfg.regularOpCost index out.toNat (writeI64 memory (out.toNat + 8) hi) lo)
      limits stack {frame with locals := frame.locals.set! 3 (.i64 lo)} callers code)) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits stack frame callers
      ([.local_get 2, .load .i64 none {align := 3, offset := 0}, .local_set 3,
        .local_get 0, .local_get 2, .i32_const 8, .i32_binop .add,
        .load .i64 none {align := 3, offset := 0}, .store .i64 none {align := 3, offset := 8},
        .local_get 0, .local_get 3, .store .i64 none {align := 3, offset := 0}] ++ code)))
      (12 * cfg.regularOpCost + rest) post := by
  let updated := {frame with locals := frame.locals.set! 3 (.i64 lo)}
  let highStore := storeI64 (paid s cfg.regularOpCost 9) index (out.toNat + 8) memory hi
  have hout' : updated.locals[0]? = some (.i32 out) := by simpa [updated, Array.set!] using hout
  have hscratch' : updated.locals[2]? = some (.i32 scratch) := by simpa [updated, Array.set!] using hscratch
  have hlo' : updated.locals[3]? = some (.i64 lo) := by simp [updated, Array.set!, hsize]
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hm7 : (paid s cfg.regularOpCost 7).modules[updated.inst]? = some mi := by simpa only [updated, paid, chargedStore] using hmodule
  have hm8 : (paid s cfg.regularOpCost 8).modules[updated.inst]? = some mi := by simpa only [updated, paid, chargedStore] using hmodule
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hmem7 : (paid s cfg.regularOpCost 7).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hmem8 : (paid s cfg.regularOpCost 8).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hmHigh : highStore.modules[updated.inst]? = some mi := by simpa only [highStore, storeI64, updated, paid, chargedStore] using hmodule
  have hmem9 : (paid s cfg.regularOpCost 9).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hmemHigh := storeI64_memory (paid s cfg.regularOpCost 9) index (out.toNat + 8) memory hi hmem9
  have hwrite := writeI64_spec memory (out.toNat + 8) hi hwf (by omega)
  have hcHigh : highStore.host.gas.Credits (3 * cfg.regularOpCost + rest) := by
    apply paid_credits s cfg.regularOpCost 9
    exact hc.mono (by omega)
  have hfinal := wp_storeWord cfg fuel rest highStore limits stack updated callers code 3
    {align := 3, offset := 0} out lo mi index (writeI64 memory (out.toNat + 8) hi) post
    hout' hlo' hmHigh hindex hmemHigh (by rw [hwrite.2.1]; change out.toNat + 0 + 8 ≤ memory.byteSize; omega)
    hcHigh hnext
  rw [show 12 * cfg.regularOpCost + rest = cfg.regularOpCost + (11 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 11) (11 * cfg.regularOpCost + rest) s limits stack frame callers _ 2 (.i32 scratch) post hscratch
    (hc.mono (by omega))
  rw [show 11 * cfg.regularOpCost + rest = cfg.regularOpCost + (10 * cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 10) (10 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits stack frame callers _
    {align := 3, offset := 0} scratch mi index memory post hm1 hindex hmem1
    (by change scratch.toNat + 0 + 8 ≤ memory.byteSize; omega)
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  simp only [Nat.add_zero, hlow]
  rw [show 10 * cfg.regularOpCost + rest = cfg.regularOpCost + (9 * cfg.regularOpCost + rest) by omega]
  apply wp_local_set cfg (fuel + 9) (9 * cfg.regularOpCost + rest) _ limits stack frame callers _ 3 (.i64 lo) post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  rw [show 9 * cfg.regularOpCost + rest = cfg.regularOpCost + (8 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 8) (8 * cfg.regularOpCost + rest) _ limits stack updated callers _ 0 (.i32 out) post hout'
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 7) (7 * cfg.regularOpCost + rest) _ limits _ updated callers _ 2 (.i32 scratch) post hscratch'
  · apply paid_credits s cfg.regularOpCost 4; exact hc.mono (by omega)
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 6) (6 * cfg.regularOpCost + rest) _ limits _ updated callers _ 8 post
  · apply paid_credits s cfg.regularOpCost 5; exact hc.mono (by omega)
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 5) (5 * cfg.regularOpCost + rest) _ limits _ updated callers _ scratch 8 post
  · apply paid_credits s cfg.regularOpCost 6; exact hc.mono (by omega)
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 7) limits _ updated callers _
    {align := 3, offset := 0} (scratch + 8) mi index memory post hm7 hindex hmem7
    (by change (scratch + 8).toNat + 0 + 8 ≤ memory.byteSize; rw [hplus]; omega)
  · apply paid_credits s cfg.regularOpCost 7; exact hc.mono (by omega)
  simp only [Nat.add_zero, hplus, hhigh]
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i64_store cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 8) limits stack updated callers _
    {align := 3, offset := 8} out hi mi index memory post hm8 hindex hmem8 (by change out.toNat + 8 + 8 ≤ memory.byteSize; omega)
  · apply paid_credits s cfg.regularOpCost 8; exact hc.mono (by omega)
  · exact hfinal

/-- The entire actual f414 body, including its real call to f566. The only
continuation is after all 29 own instructions and the completed nested call.
No source/output/scratch disjointness or execution-success premise occurs. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (globalIndex memoryIndex helperAddress : Nat)
    (global : GlobalInst) (memory : Memory) (sp out source : UInt32) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hsource : frame.locals[1]? = some (.i32 source))
    (hsize : 3 < frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hspValue : global.value = .i32 sp)
    (hhelper : mi.funcAddrs[566]? = some helperAddress)
    (hfunction : s.funcs[helperAddress]? = some (.wasm WNear.Binary.StorePair.signature frame.inst WNear.Binary.StorePair.function))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (houtBound : out.toNat + 16 ≤ memory.byteSize) (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (46 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out memory
        (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))) limits stack.toArray
      {frame with locals := (frame.locals.set! 2 (.i32 (sp - 16))).set! 3 (.i64 (readI64 memory source.toNat))}
      callers code)) rest post) :
    WP cfg (fuel + 36) (.next (atCode s limits stack.toArray frame callers (body ++ code)))
      (46 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let lo := readI64 memory source.toNat
  let hi := readI64 memory (source.toNat + 8)
  let scratch := sp - 16
  let f1 := {frame with locals := frame.locals.set! 2 (.i32 scratch)}
  let f2 := {f1 with locals := f1.locals.set! 3 (.i64 lo)}
  let s5 := reserved s op globalIndex sp
  let s12 := paid s5 op 7
  let s30 := scratchStore s op globalIndex memoryIndex sp memory lo hi
  let s42 := outputStore s op globalIndex memoryIndex sp out memory lo hi
  let scratchMemory := pairMemory memory scratch.toNat lo hi
  have hgi := (Array.getElem?_eq_some_iff.mp hglobal).1
  have hgv := (Array.getElem?_eq_some_iff.mp hglobal).2
  have f1source : f1.locals[1]? = some (.i32 source) := by simpa [f1, Array.set!] using hsource
  have f1out : f1.locals[0]? = some (.i32 out) := by simpa [f1, Array.set!] using hout
  have f1scratch : f1.locals[2]? = some (.i32 scratch) := by simp [f1, Array.set!, show 2 < frame.locals.size by omega]
  have f1size : 3 < f1.locals.size := by simpa [f1, Array.set!] using hsize
  have f2scratch : f2.locals[2]? = some (.i32 scratch) := by simpa [f2, Array.set!] using f1scratch
  have scratchBound : scratch.toNat + 16 ≤ memory.byteSize := (StorePairAddresses.scratch_bounds memory sp hsp hstack).1
  have scratchSpec := pairMemory_spec memory scratch.toNat lo hi hwf scratchBound
  have hm5 : s5.modules[f1.inst]? = some mi := by simpa only [s5, reserved, setGlobal, paid, chargedStore, f1] using hmodule
  have hm12 : s12.modules[f1.inst]? = some mi := by simpa only [s12, paid, chargedStore] using hm5
  have hm30 : s30.modules[f1.inst]? = some mi := by
    simpa only [s30, scratchStore, pairStore, storeWord, storeI64, charge3, nestedEntry, paid, reserved, setGlobal, chargedStore, f1] using hmodule
  have hm42 : s42.modules[f2.inst]? = some mi := by
    simpa only [s42, outputStore, outputHighStore, scratchStore, pairStore, storeWord, storeI64, charge3, nestedEntry, paid, reserved, setGlobal, chargedStore, f2, f1] using hmodule
  have hmem5 : s5.mems[memoryIndex]? = some memory := by simpa only [s5, reserved, setGlobal, paid, chargedStore] using hmemory
  have hmem12 : s12.mems[memoryIndex]? = some memory := by simpa only [s12, paid, chargedStore] using hmem5
  have hfn12 : s12.funcs[helperAddress]? = some (.wasm WNear.Binary.StorePair.signature f1.inst WNear.Binary.StorePair.function) := by
    simpa only [s12, s5, paid, reserved, setGlobal, chargedStore, f1] using hfunction
  have henteredMem : (nestedEntry s op globalIndex sp).mems[memoryIndex]? = some memory := by
    simpa only [nestedEntry, chargedStore, s12, s5] using hmem12
  have hmemScratch := pairStore_memory (nestedEntry s op globalIndex sp) op memoryIndex scratch.toNat memory lo hi henteredMem
  have hmem30 : s30.mems[memoryIndex]? = some scratchMemory := by
    simpa only [s30, scratchStore, scratch, scratchMemory] using hmemScratch
  have hg42 : s42.globals[globalIndex]? = some {global with value := .i32 scratch} := by
    simp [s42, outputStore, outputHighStore, scratchStore, pairStore, storeWord, storeI64, charge3, nestedEntry,
      reserved, paid, chargedStore, setGlobal, Array.getElem_modify, hgi, hgv, scratch]
  have c5' := paid_credits s op 5 (41 * op + rest) (hc.mono (by dsimp only [op]; omega))
  have c5 : s5.host.gas.Credits (41 * op + rest) := by
    simpa only [s5, reserved, setGlobal] using c5' 
  have c12 : s12.host.gas.Credits (34 * op + rest) := paid_credits s5 op 7 _ (c5.mono (by omega))
  have c13 := charged_credits s12 op (33 * op + rest) (c12.mono (by omega))
  have c24' := charged_credits (chargedStore s12 op) (11 * op) (22 * op + rest) (c13.mono (by omega))
  have c24 : (nestedEntry s op globalIndex sp).host.gas.Credits (22 * op + rest) := by
    simpa only [nestedEntry, s12, s5] using c24' 
  have c27 := storeWord_credits (nestedEntry s op globalIndex sp) op memoryIndex (scratch.toNat + 8)
    (19 * op + rest) memory hi (c24.mono (by omega))
  have c30' := storeWord_credits (storeWord (nestedEntry s op globalIndex sp) op memoryIndex (scratch.toNat + 8) memory hi)
      op memoryIndex scratch.toNat (16 * op + rest) (writeI64 memory (scratch.toNat + 8) hi) lo (c27.mono (by omega))
  have c30 : s30.host.gas.Credits (16 * op + rest) := by
    simpa only [s30, scratchStore, pairStore, scratch] using c30' 
  have c39' := paid_credits s30 op 9 (7 * op + rest) (c30.mono (by omega))
  have c39 : (outputHighStore s op globalIndex memoryIndex sp out memory lo hi).host.gas.Credits (7 * op + rest) := by
    simpa only [outputHighStore, s30, storeI64] using c39' 
  have c42' := storeWord_credits (outputHighStore s op globalIndex memoryIndex sp out memory lo hi) op memoryIndex out.toNat (4 * op + rest)
      (writeI64 scratchMemory (out.toNat + 8) hi) lo (c39.mono (by omega))
  have c42 : s42.host.gas.Credits (4 * op + rest) := by
    simpa only [s42, outputStore, scratchMemory, scratch] using c42' 
  have hrestore := wp_restore cfg fuel rest s42 limits stack.toArray f2 callers code mi globalIndex
    {global with value := .i32 scratch} scratch post f2scratch hm42 hglobalIndex hg42 c42
    (by simpa only [finalStore, s42, f2, f1, scratch, lo, hi, op, StorePairAddresses.restore] using hnext)
  have houtputStore : storeWord (storeI64 (paid s30 cfg.regularOpCost 9) memoryIndex (out.toNat + 8) scratchMemory hi)
      cfg.regularOpCost memoryIndex out.toNat (writeI64 scratchMemory (out.toNat + 8) hi) lo = s42 := by
    simp only [s42, outputStore, outputHighStore, s30, scratchMemory, scratch, op]
  have houtputNext : WP cfg (fuel + 4) (.next (atCode
      (storeWord (storeI64 (paid s30 cfg.regularOpCost 9) memoryIndex (out.toNat + 8) scratchMemory hi)
        cfg.regularOpCost memoryIndex out.toNat (writeI64 scratchMemory (out.toNat + 8) hi) lo)
      limits stack.toArray {f1 with locals := f1.locals.set! 3 (.i64 lo)} callers
      ([.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code))) (4 * op + rest) post := by
    rw [houtputStore]
    exact hrestore
  have scratchWf : scratchMemory.wf := by simpa only [scratchMemory] using scratchSpec.1
  have scratchPlus : (scratch + 8).toNat = scratch.toNat + 8 := by
    simpa only [scratch] using StorePairAddresses.scratch_add_eight sp hsp
  have scratchBound' : scratch.toNat + 16 ≤ scratchMemory.byteSize := by
    simp only [scratchMemory, scratchSpec.2.1]
    exact scratchBound
  have outBound' : out.toNat + 16 ≤ scratchMemory.byteSize := by
    simp only [scratchMemory, scratchSpec.2.1]
    exact houtBound
  have readLow : readI64 scratchMemory scratch.toNat = lo := by
    simpa only [scratchMemory] using StorePairReadback.pairMemory_read_low memory scratch.toNat lo hi hwf scratchBound
  have readHigh : readI64 scratchMemory (scratch.toNat + 8) = hi := by
    simpa only [scratchMemory] using StorePairReadback.pairMemory_read_high memory scratch.toNat lo hi hwf scratchBound
  have copyCredits : s30.host.gas.Credits (12 * cfg.regularOpCost + (4 * op + rest)) :=
    c30.mono (by dsimp only [op]; omega)
  have outputRule := wp_output cfg (fuel + 4) (4 * op + rest) s30 limits stack.toArray f1 callers
    ([.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code) mi memoryIndex scratchMemory scratch out lo hi post
  have outputLocals := outputRule f1scratch f1out f1size
  have outputEnvironment := outputLocals hm30 hmemoryIndex hmem30
  have outputMemory := outputEnvironment scratchWf scratchPlus scratchBound' outBound' readLow readHigh
  have outputPayable := outputMemory copyCredits
  have houtput := outputPayable houtputNext
  rw [show 12 * cfg.regularOpCost + (4 * op + rest) = 16 * op + rest by dsimp only [op]; omega] at houtput
  have hnestedStore : pairStore (chargedStore (chargedStore s12 cfg.regularOpCost) (11 * cfg.regularOpCost))
      cfg.regularOpCost memoryIndex scratch.toNat memory lo hi = s30 := by
    simp only [s30, scratchStore, nestedEntry, s12, s5, scratch, op]
  have hnested := wp_nested_helper cfg (fuel + 16) (16 * op + rest) s12 limits stack f1 callers
    ([.local_get 2, .load .i64 none {align := 3, offset := 0}, .local_set 3,
      .local_get 0, .local_get 2, .i32_const 8, .i32_binop .add, .load .i64 none {align := 3, offset := 0},
      .store .i64 none {align := 3, offset := 8}, .local_get 0, .local_get 3, .store .i64 none {align := 3, offset := 0},
      .local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code)
    helperAddress mi memoryIndex memory scratch lo hi post hm12 hhelper hfn12 hmemoryIndex hmem12 hwf scratchBound
    hdepth (c12.mono (by dsimp only [op]; omega))
    (by rw [hnestedStore]; simpa only [List.append, List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using houtput)
  rw [show 18 * cfg.regularOpCost + (16 * op + rest) = 34 * op + rest by dsimp only [op]; omega] at hnested
  have hstackValues : (stack ++ [Value.i32 scratch, Value.i64 lo, Value.i64 hi]).toArray =
      ((stack.toArray.push (.i32 scratch)).push (.i64 lo)).push (.i64 hi) := by
    apply Array.toList_inj.mp
    simp
  rw [hstackValues] at hnested
  have hload := wp_load_arguments cfg (fuel + 24) (34 * op + rest) s5 limits stack.toArray f1 callers
    (.call 566 :: ([.local_get 2, .load .i64 none {align := 3, offset := 0}, .local_set 3,
      .local_get 0, .local_get 2, .i32_const 8, .i32_binop .add, .load .i64 none {align := 3, offset := 0},
      .store .i64 none {align := 3, offset := 8}, .local_get 0, .local_get 3, .store .i64 none {align := 3, offset := 0},
      .local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code))
    mi memoryIndex memory scratch source post f1scratch f1source hm5 hmemoryIndex hmem5
    (StorePairAddresses.add_eight_memory memory source hwidth hsourceBound) hsourceBound
    (c5.mono (by dsimp only [op]; omega))
    (by simpa only [lo, hi, s12] using hnested)
  rw [show 7 * cfg.regularOpCost + (34 * op + rest) = 41 * op + rest by dsimp only [op]; omega] at hload
  have hstart := wp_prologue cfg (fuel + 31) (41 * op + rest) s limits stack.toArray frame callers
    ([.local_get 2, .local_get 1, .load .i64 none {align := 3, offset := 0},
      .local_get 1, .i32_const 8, .i32_binop .add, .load .i64 none {align := 3, offset := 0}, .call 566,
      .local_get 2, .load .i64 none {align := 3, offset := 0}, .local_set 3,
      .local_get 0, .local_get 2, .i32_const 8, .i32_binop .add, .load .i64 none {align := 3, offset := 0},
      .store .i64 none {align := 3, offset := 8}, .local_get 0, .local_get 3, .store .i64 none {align := 3, offset := 0},
      .local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code)
    mi globalIndex global sp post hmodule hglobalIndex hglobal hspValue (hc.mono (by dsimp only [op]; omega))
    (by simpa only [f1, scratch, s5, reserved, List.append, List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd, op] using hload)
  simpa only [body, WNear.Binary.StorePairCaller.body, List.append, List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show 5 * cfg.regularOpCost + (41 * op + rest) = 46 * cfg.regularOpCost + rest by dsimp only [op]; omega] using hstart

/-- Closed normal-return WP for the actual root frame: 29 own instructions,
six nested instructions, and two free frame leaves. -/
theorem wp_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32) (mi : ModuleInst)
    (globalIndex memoryIndex helperAddress : Nat) (global : GlobalInst) (memory : Memory) (sp : UInt32)
    (hmodule : s.modules[inst]? = some mi) (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hspValue : global.value = .i32 sp)
    (hhelper : mi.funcAddrs[566]? = some helperAddress)
    (hfunction : s.funcs[helperAddress]? = some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (houtBound : out.toNat + 16 ≤ memory.byteSize) (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) (hc : s.host.gas.Credits (46 * cfg.regularOpCost + rest)) :
    WP cfg 37 (.next (atCode s limits #[]
      (voidFrame #[.i32 out, .i32 source, .i32 0, .i64 0] inst) [] body))
      (46 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧ final = .done []
        (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out memory
          (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))) ∧ error = none) := by
  let lo := readI64 memory source.toNat
  let hi := readI64 memory (source.toNat + 8)
  let terminal := finalStore s cfg.regularOpCost globalIndex memoryIndex sp out memory lo hi
  let post : Post := fun remaining final error => remaining = rest ∧ final = .done [] terminal ∧ error = none
  have hterminal : terminal.host.gas.Credits rest := (finalStore_gas s cfg.regularOpCost globalIndex memoryIndex rest
    sp out memory lo hi hc).2.2
  have hfinish := wp_finish_void cfg 0 rest terminal limits
    #[.i32 out, .i32 source, .i32 (sp - 16), .i64 lo] inst post hterminal ⟨rfl, rfl, rfl⟩
  have hcontinuation : WP cfg 1 (.next (atCode terminal limits #[]
      {voidFrame #[.i32 out, .i32 source, .i32 0, .i64 0] inst with
        locals := (#[.i32 out, .i32 source, .i32 0, .i64 0].set! 2 (.i32 (sp - 16))).set! 3 (.i64 lo)}
      [] [])) rest post := by
    simpa [voidFrame, Array.set!] using hfinish
  have h := wp_body cfg 1 rest s limits [] (voidFrame #[.i32 out, .i32 source, .i32 0, .i64 0] inst) [] []
    mi globalIndex memoryIndex helperAddress global memory sp out source post rfl rfl (by simp [voidFrame])
    hmodule hglobalIndex hglobal hspValue hhelper hfunction hmemoryIndex hmemory hwf hwidth hsp hstack
    houtBound hsourceBound hdepth hc hcontinuation
  simpa only [List.append_nil] using h

/-- Actual metered interpreter execution terminates normally; no successful
execution or whole-method callback is assumed. Entry activation is separate. -/
theorem run_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32) (mi : ModuleInst)
    (globalIndex memoryIndex helperAddress : Nat) (global : GlobalInst) (memory : Memory) (sp : UInt32)
    (hmodule : s.modules[inst]? = some mi) (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hspValue : global.value = .i32 sp)
    (hhelper : mi.funcAddrs[566]? = some helperAddress)
    (hfunction : s.funcs[helperAddress]? = some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (houtBound : out.toNat + 16 ≤ memory.byteSize) (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) (hc : s.host.gas.Credits (46 * cfg.regularOpCost + rest)) :
    runMetered cfg 37 (.next (atCode s limits #[]
      (voidFrame #[.i32 out, .i32 source, .i32 0, .i64 0] inst) [] body)) =
      (.done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out memory
        (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))), none) := by
  obtain ⟨_, hp, _⟩ := (wp_return cfg rest s limits inst out source mi globalIndex memoryIndex helperAddress
    global memory sp hmodule hglobalIndex hglobal hspValue hhelper hfunction hmemoryIndex hmemory hwf hwidth
    hsp hstack houtBound hsourceBound hdepth hc).result
  exact Prod.ext hp.2.1 hp.2.2

end WNear.Proofs.StorePairCaller
