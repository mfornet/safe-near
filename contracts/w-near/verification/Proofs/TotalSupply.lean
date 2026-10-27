import Binary.TotalSupply
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules
import Model.Contract

/-! Top-down contracts for the actual ft_total_supply wrapper. The STATE
representation and JSON result are independent model data. Local callee
contracts describe a single returning call, never the whole method. -/
namespace WNear.Proofs.TotalSupply
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.StorePair (voidFrame wp_finish_void)
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

/-- Original model state is represented by its exact persistent STATE record.
Other account records are part of the unchanged original storage relation. -/
structure OriginalState (host : NearState) (state : WNear.State) : Prop where
  wellFormed : state.WF
  header : host.storage WNear.stateKey = some (WNear.header state)

/-- The JSON string encoding of U128 is the actual independent model's return
value, including the surrounding quotes. -/
def supplyReturn (state : WNear.State) : ReturnData := WNear.encodeRet (.u128 state.totalSupply)

theorem supplyReturn_bytes (state : WNear.State) :
    supplyReturn state = .value (WNear.jsonU128 state.totalSupply).toUTF8.toList := rfl

/-- A local normal-return contract at one actual direct-call opcode. It pays
that opcode, callee activation and execution, and restores the saved wrapper
frame at the untouched code suffix. The residual-credit clause is local too. -/
structure CalleeContract (cfg : WasmConfig) (limits : ExecLimits) (frame : CallFrame)
    (functionIndex : Nat) (args : List Value) (before after : Store NearState)
    (cost steps : Nat) : Prop where
  credits : ∀ rest, before.host.gas.Credits (cost + rest) → after.host.gas.Credits rest
  wp : ∀ fuel rest code post,
    before.host.gas.Credits (cost + rest) →
    WP cfg fuel (.next (atCode after limits #[] frame [] code)) rest post →
    WP cfg (fuel + steps) (.next (atCode before limits args.toArray frame [] (.call functionIndex :: code)))
      (cost + rest) post

/-- Pointer construction shared by every stack-relative argument group of
f296; the local is read and UInt32 addition has Wasm wrapping semantics. -/
theorem wp_pointer (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch offset : UInt32) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (stack.push (.i32 (scratch + offset))) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 0, .i32_const offset, .i32_binop .add] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 scratch) post hlocal
    (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits _ frame callers _ offset post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  apply wp_i32_add cfg fuel rest _ limits stack frame callers code scratch offset post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- Both pointer arguments are built by actual scalar instructions. -/
theorem wp_pointers (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch first second : UInt32) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid (paid s cfg.regularOpCost 3) cfg.regularOpCost 3) limits
      ((stack.push (.i32 (scratch + first))).push (.i32 (scratch + second))) frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get 0, .i32_const first, .i32_binop .add,
        .local_get 0, .i32_const second, .i32_binop .add] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  have c3 := paid_credits s cfg.regularOpCost 3 (3 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have secondRule := wp_pointer cfg fuel rest (paid s cfg.regularOpCost 3) limits
    (stack.push (.i32 (scratch + first))) frame callers code scratch second post
  have hsecond := secondRule hlocal c3 hnext
  have firstRule := wp_pointer cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.local_get 0, .i32_const second, .i32_binop .add] ++ code) scratch first post
  have firstCredit : s.host.gas.Credits (3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have hfirst := firstRule hlocal firstCredit hsecond
  simpa only [List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show 3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 6 * cfg.regularOpCost + rest by omega] using hfirst

theorem wp_prologue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (sp : UInt32) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 5) index (.i32 (sp - 144))) limits stack
      {frame with locals := frame.locals.set! 0 (.i32 (sp - 144))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.global_get 0, .i32_const 144, .i32_binop .sub, .local_tee 0, .global_set 0] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have h1 := paid_credits s cfg.regularOpCost 1 (4 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h2 := paid_credits s cfg.regularOpCost 2 (3 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h3 := paid_credits s cfg.regularOpCost 3 (2 * cfg.regularOpCost + rest) (hc.mono (by omega))
  have h4 := paid_credits s cfg.regularOpCost 4 (cfg.regularOpCost + rest) (hc.mono (by omega))
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg4 : (paid s cfg.regularOpCost 4).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  have hget := wp_global_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.i32_const 144, .i32_binop .sub, .local_tee 0, .global_set 0] ++ code)
    0 index mi global post hmodule hindex hglobal h0
  rw [hsp] at hget
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply hget
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 144 post
    (by simpa only [paid, show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega] using h1)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_sub cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits stack frame callers _ sp 144 post
    (by simpa only [paid, show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega] using h2)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ 0 (.i32 (sp - 144)) post
    (by simpa only [paid, show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega] using h3)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 4) limits stack {frame with locals := frame.locals.set! 0 (.i32 (sp - 144))} callers code 0 index mi (.i32 (sp - 144)) global post
    hm4 hindex hg4
  · simpa only [paid] using h4
  · simpa only [paid] using hnext


theorem wp_restore (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (scratch : UInt32) (post : Post)
    (hscratch : frame.locals[0]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.globalAddrs[0]? = some index)
    (hglobal : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 144))) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 0, .i32_const 144, .i32_binop .add, .global_set 0] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hg3 : (paid s cfg.regularOpCost 3).globals[index]? = some global := by simpa only [paid, chargedStore] using hglobal
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 scratch) post hscratch
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 144 post
  · apply paid_credits s cfg.regularOpCost 1
    exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits stack frame callers _ scratch 144 post
  · apply paid_credits s cfg.regularOpCost 2
    exact hc.mono (by omega)
  apply wp_global_set cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 0 index mi (.i32 (scratch + 144)) global post
    hm3 hindex hg3
  · apply paid_credits s cfg.regularOpCost 3
    exact hc.mono (by omega)
  · simpa only [paid] using hnext


/-- The fixed arguments of the interface-installation call use two opcodes. -/
theorem wp_interface_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (post : Post)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits
      ((stack.push (.i32 1)).push (.i32 1050188)) frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers
      ([.i32_const 1, .i32_const 1050188] ++ code))) (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) (cfg.regularOpCost + rest) s limits stack frame callers _ 1 post
    (hc.mono (by omega))
  apply wp_i32_const cfg fuel rest _ limits _ frame callers code 1050188 post
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- Result.expect receives both stack-relative pointers and its static message. -/
theorem wp_expect_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (chargedStore (paid (paid s cfg.regularOpCost 3) cfg.regularOpCost 3) cfg.regularOpCost) limits
      (((stack.push (.i32 (scratch + 128))).push (.i32 (scratch + 72))).push (.i32 1050984))
      frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      ([.local_get 0, .i32_const 128, .i32_binop .add,
        .local_get 0, .i32_const 72, .i32_binop .add, .i32_const 1050984] ++ code)))
      (7 * cfg.regularOpCost + rest) post := by
  have c6 : (paid (paid s cfg.regularOpCost 3) cfg.regularOpCost 3).host.gas.Credits
      (cfg.regularOpCost + rest) := by
    apply paid_credits
    apply paid_credits
    exact hc.mono (by omega)
  have constRule := wp_i32_const cfg fuel rest (paid (paid s cfg.regularOpCost 3) cfg.regularOpCost 3)
    limits ((stack.push (.i32 (scratch + 128))).push (.i32 (scratch + 72))) frame callers code 1050984 post
  have hconst := constRule c6 hnext
  have pointerRule := wp_pointers cfg (fuel + 1) (cfg.regularOpCost + rest) s limits stack frame callers
    (.i32_const 1050984 :: code) scratch 128 72 post
  have cp : s.host.gas.Credits (6 * cfg.regularOpCost + (cfg.regularOpCost + rest)) := hc.mono (by omega)
  have hp := pointerRule hlocal cp hconst
  simpa only [List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show 6 * cfg.regularOpCost + (cfg.regularOpCost + rest) = 7 * cfg.regularOpCost + rest by omega] using hp

/-- The pointer/length pair passed to value_return is loaded from the actual
Vec.deref output. Both loads execute; no load-result contract is assumed. -/
theorem wp_return_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : scratch.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 (readI32 memory (scratch.toNat + 8)))).push
        (.i32 (readI32 memory (scratch.toNat + 12)))) frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 0, .load .i32 none {align := 2, offset := 8},
        .local_get 0, .load .i32 none {align := 2, offset := 12}] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 scratch) post hlocal
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) (2 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits stack frame callers _
    {align := 2, offset := 8} scratch mi index memory post hm1 hindex hmem1
  · change scratch.toNat + 8 + 4 ≤ memory.byteSize; omega
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) (cfg.regularOpCost + rest) _ limits _ frame callers _ 0 (.i32 scratch) post hlocal
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  apply wp_i32_load cfg fuel rest (paid s cfg.regularOpCost 3) limits _ frame callers code
    {align := 2, offset := 12} scratch mi index memory post hm3 hindex hmem3
  · change scratch.toNat + 12 + 4 ≤ memory.byteSize; omega
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- A directly addressed copy, with the source read before the destination write.
This is the four-instruction low-word copy in f296. -/
theorem wp_copy_word (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (source destination : Nat)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hread : scratch.toNat + source + 8 ≤ memory.byteSize)
    (hwrite : scratch.toNat + destination + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI64 (paid s cfg.regularOpCost 4) index (scratch.toNat + destination) memory
        (readI64 memory (scratch.toNat + source))) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 0, .load .i64 none {align := 3, offset := source},
        .store .i64 none {align := 3, offset := destination}] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 scratch) post hlocal
    (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ 0 (.i32 scratch) post hlocal
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 3, offset := source} scratch mi index memory post hm2 hindex hmem2 hread
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 3, offset := destination} scratch (readI64 memory (scratch.toNat + source)) mi index memory post
    hm3 hindex hmem3 hwrite
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  · simpa only [paid] using hnext

/-- The six-instruction high-word copy computes scratch+24 before loading.
The destination is scratch+120, so its exact sequential memory is explicit. -/
theorem wp_copy_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory)
    (hread : (scratch + 24).toNat + 8 ≤ memory.byteSize)
    (hwrite : scratch.toNat + 128 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI64 (paid s cfg.regularOpCost 6) index (scratch.toNat + 120) memory
        (readI64 memory (scratch + 24).toNat)) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 0, .i32_const 24, .i32_binop .add,
        .load .i64 none {align := 3, offset := 0}, .store .i64 none {align := 3, offset := 120}] ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hm5 : (paid s cfg.regularOpCost 5).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hmem5 : (paid s cfg.regularOpCost 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmemory
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) (5 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 scratch) post hlocal
    (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) _ limits _ frame callers _ 0 (.i32 scratch) post hlocal
  · apply paid_credits s cfg.regularOpCost 1; exact hc.mono (by omega)
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) _ limits _ frame callers _ 24 post
  · apply paid_credits s cfg.regularOpCost 2; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame callers _ scratch 24 post
  · apply paid_credits s cfg.regularOpCost 3; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 1) (cfg.regularOpCost + rest) (paid s cfg.regularOpCost 4) limits _ frame callers _
    {align := 3, offset := 0} (scratch + 24) mi index memory post hm4 hindex hmem4
  · simpa only [Nat.add_zero] using hread
  · apply paid_credits s cfg.regularOpCost 4; exact hc.mono (by omega)
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 5) limits stack frame callers code
    {align := 3, offset := 120} scratch (readI64 memory (scratch + 24).toNat) mi index memory post hm5 hindex hmem5
  · change scratch.toNat + 120 + 8 ≤ memory.byteSize; omega
  · apply paid_credits s cfg.regularOpCost 5; exact hc.mono (by omega)
  · simpa only [paid, Nat.add_zero] using hnext

/-- Actual first write of the serializer-input copy. -/
def copyHighStore (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory) : Store NearState :=
  storeI64 (paid s op 6) index (scratch.toNat + 120) memory (readI64 memory (scratch + 24).toNat)

/-- Exact memory after the high word is written, before the low word is read. -/
def highMemory (memory : Memory) (scratch : UInt32) : Memory :=
  writeI64 memory (scratch.toNat + 120) (readI64 memory (scratch + 24).toNat)

/-- Actual second write; its source is read from the first write's memory. -/
def copyStore (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory) : Store NearState :=
  storeI64 (paid (copyHighStore s op index scratch memory) op 4) index (scratch.toNat + 112)
    (highMemory memory scratch) (readI64 (highMemory memory scratch) (scratch.toNat + 16))

/-- The complete ten-instruction serializer-input copy, including both loads
and both stores. Bounds are explicit and no pure-execution callback is used. -/
theorem wp_copy_pair (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 scratch))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : (scratch + 24).toNat + 8 ≤ memory.byteSize)
    (hwrite : scratch.toNat + 128 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (10 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (copyStore s cfg.regularOpCost index scratch memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 10) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 0, .i32_const 24, .i32_binop .add,
        .load .i64 none {align := 3, offset := 0}, .store .i64 none {align := 3, offset := 120},
        .local_get 0, .local_get 0, .load .i64 none {align := 3, offset := 16},
        .store .i64 none {align := 3, offset := 112}] ++ code)))
      (10 * cfg.regularOpCost + rest) post := by
  have hm : (copyHighStore s cfg.regularOpCost index scratch memory).modules[frame.inst]? = some mi := by
    simpa only [copyHighStore, storeI64_modules, paid, chargedStore] using hmodule
  have hp : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by
    simpa only [paid, chargedStore] using hmemory
  have hmem : (copyHighStore s cfg.regularOpCost index scratch memory).mems[index]? =
      some (highMemory memory scratch) := storeI64_memory _ _ _ _ _ hp
  have hs := writeI64_spec memory (scratch.toNat + 120) (readI64 memory (scratch + 24).toNat) hwf
    (by omega)
  have hsize : (highMemory memory scratch).byteSize = memory.byteSize := hs.2.1
  have hlowRead : scratch.toNat + 16 + 8 ≤ (highMemory memory scratch).byteSize := by
    rw [hsize]; omega
  have hlowWrite : scratch.toNat + 112 + 8 ≤ (highMemory memory scratch).byteSize := by
    rw [hsize]; omega
  have clow : (copyHighStore s cfg.regularOpCost index scratch memory).host.gas.Credits
      (4 * cfg.regularOpCost + rest) := by
    apply paid_credits s cfg.regularOpCost 6; exact hc.mono (by omega)
  have lowRule := wp_copy_word cfg fuel rest (copyHighStore s cfg.regularOpCost index scratch memory)
    limits stack frame callers code scratch 16 112 mi index (highMemory memory scratch) post
  have lowLocal := lowRule hlocal
  have lowEnv := lowLocal hm hindex hmem
  have lowBounds := lowEnv hlowRead hlowWrite
  have lowPaid := lowBounds clow
  have hlow := lowPaid hnext
  have highRule := wp_copy_high cfg (fuel + 4) (4 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.local_get 0, .local_get 0, .load .i64 none {align := 3, offset := 16},
      .store .i64 none {align := 3, offset := 112}] ++ code) scratch mi index memory post
  have highEnv := highRule hlocal hmodule hindex hmemory
  have highBounds := highEnv hread hwrite
  have chigh : s.host.gas.Credits (6 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have hhigh := highBounds chigh hlow
  simpa only [List.append_eq, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show 6 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest) = 10 * cfg.regularOpCost + rest by omega] using hhigh

/-- Each field names one actual call site, with its exact stack-relative
arguments. Costs include the call opcode and callee activation/execution.
The repeated cleanup function has two distinct obligations. -/
structure CallObligations (cfg : WasmConfig) (limits : ExecLimits) (frame : CallFrame)
    (scratch returnPointer returnLength : UInt32)
    (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat) : Prop where
  panicHook : CalleeContract cfg limits frame 522 [] (before 0) (after 0) (cost 0) (steps 0)
  installInterface : CalleeContract cfg limits frame 520 [.i32 1, .i32 1050188] (before 1) (after 1) (cost 1) (steps 1)
  readState : CalleeContract cfg limits frame 219 [.i32 (scratch + 72)] (before 2) (after 2) (cost 2) (steps 2)
  unwrapState : CalleeContract cfg limits frame 155 [.i32 (scratch + 32), .i32 (scratch + 72)]
    (before 3) (after 3) (cost 3) (steps 3)
  readSupply : CalleeContract cfg limits frame 414 [.i32 (scratch + 16), .i32 (scratch + 32)]
    (before 4) (after 4) (cost 4) (steps 4)
  serialize : CalleeContract cfg limits frame 96 [.i32 (scratch + 72), .i32 (scratch + 112)]
    (before 5) (after 5) (cost 5) (steps 5)
  expectSerialization : CalleeContract cfg limits frame 158 [.i32 (scratch + 128), .i32 (scratch + 72), .i32 1050984]
    (before 6) (after 6) (cost 6) (steps 6)
  vectorSlice : CalleeContract cfg limits frame 779 [.i32 (scratch + 8), .i32 (scratch + 128)]
    (before 7) (after 7) (cost 7) (steps 7)
  returnValue : CalleeContract cfg limits frame 545 [.i32 returnPointer, .i32 returnLength]
    (before 8) (after 8) (cost 8) (steps 8)
  dropReturnVector : CalleeContract cfg limits frame 68 [.i32 (scratch + 128)]
    (before 9) (after 9) (cost 9) (steps 9)
  dropStateVector : CalleeContract cfg limits frame 68 [.i32 (scratch + 56)]
    (before 10) (after 10) (cost 10) (steps 10)

/-- The exact original-data U128 represented by two words in a decoded object. -/
def U128At (memory : Memory) (address value : Nat) : Prop :=
  (readI64 memory address).toNat + 2 ^ 64 * (readI64 memory (address + 8)).toNat = value

/-- JSON data reached through an actual pointer/length pair. -/
def JsonAt (memory : Memory) (pointer length : UInt32) (state : WNear.State) : Prop :=
  pointer.toNat + length.toNat ≤ memory.byteSize ∧
    (List.range length.toNat).map (fun i => memory.read8 (pointer.toNat + i)) =
      (WNear.jsonU128 state.totalSupply).toUTF8.toList

/-- Concrete functional obligations between the read/deserialize/serialize
callees. These are data-layout assertions at individual call boundaries;
none assumes execution of f296 or a successful public runtime outcome. -/
structure RepresentationObligations (original : NearState) (state : WNear.State)
    (scratch pointer length : UInt32) (unwrapped returned serialization sliced : Memory)
    (afterReturn afterDropReturn afterDropState : NearState) : Prop where
  originalState : OriginalState original state
  unwrappedSupply : U128At unwrapped (scratch + 32).toNat state.totalSupply
  copiedSupply : U128At returned (scratch + 16).toNat state.totalSupply
  serializerInput : U128At serialization (scratch + 112).toNat state.totalSupply
  slicePointer : readI32 sliced (scratch.toNat + 8) = pointer
  sliceLength : readI32 sliced (scratch.toNat + 12) = length
  serializedBytes : JsonAt sliced pointer length state
  returnedValue : afterReturn.returnData = some (WNear.jsonU128 state.totalSupply).toUTF8.toList
  returnStorage : afterReturn.storage = original.storage
  dropReturnData : afterDropReturn.returnData = afterReturn.returnData
  dropReturnStorage : afterDropReturn.storage = afterReturn.storage
  dropStateData : afterDropState.returnData = afterDropReturn.returnData
  dropStateStorage : afterDropState.storage = afterDropReturn.storage

/-- Callee effects imply the final cleanup boundary retains the independent
model's U128 return and the complete original persistent storage. -/
theorem after_cleanup (original : NearState) (state : WNear.State)
    (scratch pointer length : UInt32) (unwrapped returned serialization sliced : Memory)
    (afterReturn afterDropReturn afterDropState : NearState)
    (h : RepresentationObligations original state scratch pointer length unwrapped returned serialization sliced
      afterReturn afterDropReturn afterDropState) :
    afterDropState.returnData = some (WNear.jsonU128 state.totalSupply).toUTF8.toList ∧
    afterDropState.storage = original.storage := by
  constructor
  · exact h.dropStateData.trans (h.dropReturnData.trans h.returnedValue)
  · exact h.dropStateStorage.trans (h.dropReturnStorage.trans h.returnStorage)

/-- Concrete pure-instruction groups between the eleven deployed calls.
This list is source-level data, not an assumed execution plan. -/
def scalarChunks : List (List Instr) :=
  [
    [.global_get 0,
     .i32_const 144,
     .i32_binop .sub,
     .local_tee 0,
     .global_set 0],
    [.i32_const 1,
     .i32_const 1050188],
    [.local_get 0,
     .i32_const 72,
     .i32_binop .add],
    [.local_get 0,
     .i32_const 32,
     .i32_binop .add,
     .local_get 0,
     .i32_const 72,
     .i32_binop .add],
    [.local_get 0,
     .i32_const 16,
     .i32_binop .add,
     .local_get 0,
     .i32_const 32,
     .i32_binop .add],
    [.local_get 0,
     .local_get 0,
     .i32_const 24,
     .i32_binop .add,
     .load .i64 none {align := 3, offset := 0},
     .store .i64 none {align := 3, offset := 120},
     .local_get 0,
     .local_get 0,
     .load .i64 none {align := 3, offset := 16},
     .store .i64 none {align := 3, offset := 112},
     .local_get 0,
     .i32_const 72,
     .i32_binop .add,
     .local_get 0,
     .i32_const 112,
     .i32_binop .add],
    [.local_get 0,
     .i32_const 128,
     .i32_binop .add,
     .local_get 0,
     .i32_const 72,
     .i32_binop .add,
     .i32_const 1050984],
    [.local_get 0,
     .i32_const 8,
     .i32_binop .add,
     .local_get 0,
     .i32_const 128,
     .i32_binop .add],
    [.local_get 0,
     .load .i32 none {align := 2, offset := 8},
     .local_get 0,
     .load .i32 none {align := 2, offset := 12}],
    [.local_get 0,
     .i32_const 128,
     .i32_binop .add],
    [.local_get 0,
     .i32_const 56,
     .i32_binop .add],
    [.local_get 0,
     .i32_const 144,
     .i32_binop .add,
     .global_set 0]
  ]

/-- Interleave the concrete groups and call sites, with the final group
restoring the stack global after both cleanup calls. -/
def interleaveCalls : List (List Instr) → List Nat → List Instr
  | [], _ => []
  | group :: groups, [] => group ++ groups.flatten
  | group :: groups, callee :: callees => group ++ [.call callee] ++ interleaveCalls groups callees

theorem concrete_body :
    WNear.Binary.TotalSupply.body = interleaveCalls scalarChunks WNear.Binary.TotalSupply.callees := rfl

theorem scalar_lengths : scalarChunks.map List.length = [5, 2, 3, 6, 6, 16, 7, 6, 4, 3, 3, 4] := rfl

theorem scalar_total : (scalarChunks.map List.length).sum = 65 := rfl

theorem chunks_have_no_calls : scalarChunks.all (fun group => group.all (fun i => match i with
    | .call _ => false
    | _ => true)) = true := rfl

/-- Exact store equations that connect the eleven local callee contracts.
Every right-hand side is a concrete pure-group result proved above. These
are the structural/data obligations for future backward composition; this
record does not assert execution of the method or any pure group. -/
structure ScalarBoundaries (cfg : WasmConfig) (initial final : Store NearState)
    (before after : Fin 11 → Store NearState) (scratch : UInt32)
    (globalIndex memoryIndex : Nat) (copyMemory : Memory) : Prop where
  prologue : before 0 = setGlobal (paid initial cfg.regularOpCost 5) globalIndex (.i32 scratch)
  interfaceArgs : before 1 = paid (after 0) cfg.regularOpCost 2
  stateArgs : before 2 = paid (after 1) cfg.regularOpCost 3
  unwrapArgs : before 3 = paid (paid (after 2) cfg.regularOpCost 3) cfg.regularOpCost 3
  supplyArgs : before 4 = paid (paid (after 3) cfg.regularOpCost 3) cfg.regularOpCost 3
  serializeArgs : before 5 = paid (paid
    (copyStore (after 4) cfg.regularOpCost memoryIndex scratch copyMemory) cfg.regularOpCost 3) cfg.regularOpCost 3
  expectArgs : before 6 = chargedStore (paid (paid (after 5) cfg.regularOpCost 3) cfg.regularOpCost 3) cfg.regularOpCost
  sliceArgs : before 7 = paid (paid (after 6) cfg.regularOpCost 3) cfg.regularOpCost 3
  returnArgs : before 8 = paid (after 7) cfg.regularOpCost 4
  dropReturnArgs : before 9 = paid (after 8) cfg.regularOpCost 3
  dropStateArgs : before 10 = paid (after 9) cfg.regularOpCost 3
  restored : final = setGlobal (paid (after 10) cfg.regularOpCost 4) globalIndex (.i32 (scratch + 144))

/-- Remaining environment and native bounds at the scalar memory/global
boundaries. Callee functional proofs must establish these from their frames;
none is a whole-method execution hypothesis. -/
structure BoundaryInvariants (initial : Store NearState) (after : Fin 11 → Store NearState)
    (frame : CallFrame) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst)
    (copyMemory sliceMemory : Memory) : Prop where
  scratch_eq : scratch = sp - 144
  module_initial : initial.modules[frame.inst]? = some mi
  global_index : mi.globalAddrs[0]? = some globalIndex
  global_initial : initial.globals[globalIndex]? = some originalGlobal
  original_sp : originalGlobal.value = .i32 sp
  local_capacity : 0 < frame.locals.size
  module_copy : (after 4).modules[frame.inst]? = some mi
  memory_index : mi.memAddrs[0]? = some memoryIndex
  memory_copy : (after 4).mems[memoryIndex]? = some copyMemory
  copy_wf : copyMemory.wf
  copy_high_read : (scratch + 24).toNat + 8 ≤ copyMemory.byteSize
  copy_span : scratch.toNat + 128 ≤ copyMemory.byteSize
  module_slice : (after 7).modules[frame.inst]? = some mi
  memory_slice : (after 7).mems[memoryIndex]? = some sliceMemory
  slice_span : scratch.toNat + 16 ≤ sliceMemory.byteSize
  slice_pointer : readI32 sliceMemory (scratch.toNat + 8) = pointer
  slice_length : readI32 sliceMemory (scratch.toNat + 12) = length
  module_cleanup : (after 10).modules[frame.inst]? = some mi
  global_cleanup : (after 10).globals[globalIndex]? = some finalGlobal

/-- Static method budget recipe: 65 actual scalar opcodes plus eleven complete
local call budgets. Entry activation is nine additional regular-op units. -/
def bodyCost (cfg : WasmConfig) (cost : Fin 11 → Nat) : Nat :=
  65 * cfg.regularOpCost + ((List.finRange 11).map cost).sum

def entryCost (cfg : WasmConfig) (cost : Fin 11 → Nat) : Nat :=
  9 * cfg.regularOpCost + bodyCost cfg cost

/-- Structural body fuel excludes the final free wrapper leave. Every call
budget must separately count its call opcode, callee body and normal leave. -/
def bodySteps (steps : Fin 11 → Nat) : Nat := 65 + ((List.finRange 11).map steps).sum

/-- Exact residual credits of the serializer-input's two actual writes. -/
theorem copyStore_credits (s : Store NearState) (op index : Nat) (scratch : UInt32)
    (memory : Memory) (rest : Nat) (h : s.host.gas.Credits (10 * op + rest)) :
    (copyStore s op index scratch memory).host.gas.Credits rest := by
  change (paid (copyHighStore s op index scratch memory) op 4).host.gas.Credits rest
  apply paid_credits
  change (paid s op 6).host.gas.Credits (4 * op + rest)
  apply paid_credits
  exact h.mono (by omega)

/-- Finite sums in the exact eleven-call budget reduce without any runtime evaluation. -/
theorem eleven_sum (f : Fin 11 → Nat) :
    ((List.finRange 11).map f).sum =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + 0)))))))))) := rfl

theorem ten_six (op rest : Nat) : 10 * op + (6 * op + rest) = 16 * op + rest := by omega

theorem bodyFuel_decomposition (fuel : Nat) (steps : Fin 11 → Nat) :
    ((((((((((((((((((((((((fuel + 4) + steps 10) + 3) + steps 9) + 3) + steps 8) + 4) + steps 7) + 6) + steps 6) + 7) + steps 5) + 6) + 10) + steps 4) + 6) + steps 3) + 6) + steps 2) + 3) + steps 1) + 2) + steps 0) + 5) = fuel + bodySteps steps := by
  simp only [bodySteps, eleven_sum]
  omega

/-- Actual 76-instruction wrapper composition. The only execution contracts
assumed are the eleven named local callees. All scalar groups, intermediate
credits, memory reads/writes and stack-pointer restoration are derived here.
The final continuation starts after the concrete body, before its free leave. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (initial final : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (code : List Instr) (post : Post)
    (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hcalls : CallObligations cfg limits {frame with locals := frame.locals.set! 0 (.i32 scratch)}
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg initial final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants initial after frame mi globalIndex memoryIndex sp scratch pointer length
      originalGlobal finalGlobal copyMemory sliceMemory)
    (hc : initial.host.gas.Credits (bodyCost cfg cost + rest))
    (hnext : WP cfg fuel (.next (atCode final limits #[]
      {frame with locals := frame.locals.set! 0 (.i32 scratch)} [] code)) rest post) :
    WP cfg (fuel + bodySteps steps) (.next (atCode initial limits #[] frame []
      (WNear.Binary.TotalSupply.body ++ code))) (bodyCost cfg cost + rest) post := by
  let op := cfg.regularOpCost
  let activeFrame : CallFrame := {frame with locals := frame.locals.set! 0 (.i32 scratch)}
  have hlocal : activeFrame.locals[0]? = some (.i32 scratch) := by
    simp [activeFrame, hinv.local_capacity]
  let g10 := 4 * op + rest
  let f10 := fuel + 4
  let g9 := 3 * op + (cost 10 + g10)
  let f9 := (f10 + steps 10) + 3
  let g8 := 3 * op + (cost 9 + g9)
  let f8 := (f9 + steps 9) + 3
  let g7 := 4 * op + (cost 8 + g8)
  let f7 := (f8 + steps 8) + 4
  let g6 := 6 * op + (cost 7 + g7)
  let f6 := (f7 + steps 7) + 6
  let g5 := 7 * op + (cost 6 + g6)
  let f5 := (f6 + steps 6) + 7
  let g4 := 16 * op + (cost 5 + g5)
  let f4 := ((f5 + steps 5) + 6) + 10
  let g3 := 6 * op + (cost 4 + g4)
  let f3 := (f4 + steps 4) + 6
  let g2 := 6 * op + (cost 3 + g3)
  let f2 := (f3 + steps 3) + 6
  let g1 := 3 * op + (cost 2 + g2)
  let f1 := (f2 + steps 2) + 3
  let g0 := 2 * op + (cost 1 + g1)
  let f0 := (f1 + steps 1) + 2
  have hbudget : 5 * op + (cost 0 + g0) = bodyCost cfg cost + rest := by
    clear hcalls hboundaries hinv hc hnext hlocal
    simp only [bodyCost, eleven_sum]
    dsimp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, op]
    omega
  have initialCredit : initial.host.gas.Credits (5 * op + (cost 0 + g0)) := by
    rw [hbudget]; exact hc
  have c0 : (before 0).host.gas.Credits (cost 0 + g0) := by
    rw [hboundaries.prologue]
    apply paid_credits
    exact initialCredit
  have a0 := hcalls.panicHook.credits g0 c0
  have c1 : (before 1).host.gas.Credits (cost 1 + g1) := by
    rw [hboundaries.interfaceArgs]
    apply paid_credits
    exact a0.mono (by dsimp [g0]; omega)
  have a1 := hcalls.installInterface.credits g1 c1
  have c2 : (before 2).host.gas.Credits (cost 2 + g2) := by
    rw [hboundaries.stateArgs]
    apply paid_credits
    exact a1.mono (by dsimp [g1]; omega)
  have a2 := hcalls.readState.credits g2 c2
  have c3 : (before 3).host.gas.Credits (cost 3 + g3) := by
    rw [hboundaries.unwrapArgs]
    apply paid_credits
    apply paid_credits
    exact a2.mono (by dsimp [g2]; omega)
  have a3 := hcalls.unwrapState.credits g3 c3
  have c4 : (before 4).host.gas.Credits (cost 4 + g4) := by
    rw [hboundaries.supplyArgs]
    apply paid_credits
    apply paid_credits
    exact a3.mono (by dsimp [g3]; omega)
  have a4 := hcalls.readSupply.credits g4 c4
  have c5 : (before 5).host.gas.Credits (cost 5 + g5) := by
    rw [hboundaries.serializeArgs]
    apply paid_credits
    apply paid_credits
    apply copyStore_credits
    exact a4.mono (by dsimp [g4]; omega)
  have a5 := hcalls.serialize.credits g5 c5
  have c6 : (before 6).host.gas.Credits (cost 6 + g6) := by
    rw [hboundaries.expectArgs]
    apply WNear.Proofs.StorePair.charged_credits
    apply paid_credits
    apply paid_credits
    exact a5.mono (by dsimp [g5]; omega)
  have a6 := hcalls.expectSerialization.credits g6 c6
  have c7 : (before 7).host.gas.Credits (cost 7 + g7) := by
    rw [hboundaries.sliceArgs]
    apply paid_credits
    apply paid_credits
    exact a6.mono (by dsimp [g6]; omega)
  have a7 := hcalls.vectorSlice.credits g7 c7
  have c8 : (before 8).host.gas.Credits (cost 8 + g8) := by
    rw [hboundaries.returnArgs]
    apply paid_credits
    exact a7.mono (by dsimp [g7]; omega)
  have a8 := hcalls.returnValue.credits g8 c8
  have c9 : (before 9).host.gas.Credits (cost 9 + g9) := by
    rw [hboundaries.dropReturnArgs]
    apply paid_credits
    exact a8.mono (by dsimp [g8]; omega)
  have a9 := hcalls.dropReturnVector.credits g9 c9
  have c10 : (before 10).host.gas.Credits (cost 10 + g10) := by
    rw [hboundaries.dropStateArgs]
    apply paid_credits
    exact a9.mono (by dsimp [g9]; omega)
  have a10 := hcalls.dropStateVector.credits g10 c10
  let code10 : List Instr := [.local_get 0, .i32_const 144, .i32_binop .add, .global_set 0] ++ code
  let code9 : List Instr := [.local_get 0, .i32_const 56, .i32_binop .add] ++ (.call 68 :: code10)
  let code8 : List Instr := [.local_get 0, .i32_const 128, .i32_binop .add] ++ (.call 68 :: code9)
  let code7 : List Instr := [.local_get 0, .load .i32 none {align := 2, offset := 8}, .local_get 0, .load .i32 none {align := 2, offset := 12}] ++ (.call 545 :: code8)
  let code6 : List Instr := [.local_get 0, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 128, .i32_binop .add] ++ (.call 779 :: code7)
  let code5 : List Instr := [.local_get 0, .i32_const 128, .i32_binop .add, .local_get 0, .i32_const 72, .i32_binop .add, .i32_const 1050984] ++ (.call 158 :: code6)
  let code4 : List Instr := [.local_get 0, .local_get 0, .i32_const 24, .i32_binop .add, .load .i64 none {align := 3, offset := 0}, .store .i64 none {align := 3, offset := 120}, .local_get 0, .local_get 0, .load .i64 none {align := 3, offset := 16}, .store .i64 none {align := 3, offset := 112}, .local_get 0, .i32_const 72, .i32_binop .add, .local_get 0, .i32_const 112, .i32_binop .add] ++ (.call 96 :: code5)
  let code3 : List Instr := [.local_get 0, .i32_const 16, .i32_binop .add, .local_get 0, .i32_const 32, .i32_binop .add] ++ (.call 414 :: code4)
  let code2 : List Instr := [.local_get 0, .i32_const 32, .i32_binop .add, .local_get 0, .i32_const 72, .i32_binop .add] ++ (.call 155 :: code3)
  let code1 : List Instr := [.local_get 0, .i32_const 72, .i32_binop .add] ++ (.call 219 :: code2)
  let code0 : List Instr := [.i32_const 1, .i32_const 1050188] ++ (.call 520 :: code1)
  have hfinal : WP cfg fuel (.next (atCode
      (setGlobal (paid (after 10) cfg.regularOpCost 4) globalIndex (.i32 (scratch + 144)))
      limits #[] activeFrame [] code)) rest post := by
    simpa only [← hboundaries.restored] using hnext
  have restoreRule := wp_restore cfg fuel rest (after 10) limits #[] activeFrame [] code
    mi globalIndex finalGlobal scratch post
  have restoreLocal := restoreRule hlocal
  have restoreEnv := restoreLocal hinv.module_cleanup hinv.global_index hinv.global_cleanup
  have h10 := restoreEnv a10 hfinal
  have call10 := hcalls.dropStateVector.wp f10 g10 code10 post c10 h10
  rw [hboundaries.dropStateArgs] at call10
  have argRule9 := wp_pointer cfg (f10 + steps 10) (cost 10 + g10)
    (after 9) limits #[] activeFrame [] (.call 68 :: code10) scratch 56 post
  have argLocal9 := argRule9 hlocal
  have h9 := argLocal9 a9 call10
  have call9 := hcalls.dropReturnVector.wp f9 g9 code9 post c9 h9
  rw [hboundaries.dropReturnArgs] at call9
  have argRule8 := wp_pointer cfg (f9 + steps 9) (cost 9 + g9)
    (after 8) limits #[] activeFrame [] (.call 68 :: code9) scratch 128 post
  have argLocal8 := argRule8 hlocal
  have h8 := argLocal8 a8 call9
  have call8 := hcalls.returnValue.wp f8 g8 code8 post c8 h8
  rw [hboundaries.returnArgs] at call8
  rw [← hinv.slice_pointer, ← hinv.slice_length] at call8
  have argRule7 := wp_return_arguments cfg (f8 + steps 8) (cost 8 + g8)
    (after 7) limits #[] activeFrame [] (.call 545 :: code8) scratch mi memoryIndex sliceMemory post
  have argLocal7 := argRule7 hlocal
  have argEnv7 := argLocal7 hinv.module_slice hinv.memory_index hinv.memory_slice
  have argBounds7 := argEnv7 hinv.slice_span
  have h7 := argBounds7 a7 call8
  have call7 := hcalls.vectorSlice.wp f7 g7 code7 post c7 h7
  rw [hboundaries.sliceArgs] at call7
  have argRule6 := wp_pointers cfg (f7 + steps 7) (cost 7 + g7)
    (after 6) limits #[] activeFrame [] (.call 779 :: code7) scratch 8 128 post
  have argLocal6 := argRule6 hlocal
  have h6 := argLocal6 a6 call7
  have call6 := hcalls.expectSerialization.wp f6 g6 code6 post c6 h6
  rw [hboundaries.expectArgs] at call6
  have argRule5 := wp_expect_arguments cfg (f6 + steps 6) (cost 6 + g6)
    (after 5) limits #[] activeFrame [] (.call 158 :: code6) scratch post
  have argLocal5 := argRule5 hlocal
  have h5 := argLocal5 a5 call6
  have call5 := hcalls.serialize.wp f5 g5 code5 post c5 h5
  rw [hboundaries.serializeArgs] at call5
  let copied := copyStore (after 4) cfg.regularOpCost memoryIndex scratch copyMemory
  have copiedCredit : copied.host.gas.Credits (6 * cfg.regularOpCost + (cost 5 + g5)) := by
    apply copyStore_credits
    exact a4.mono (by dsimp [g4, op]; omega)
  have pointerRule4 := wp_pointers cfg (f5 + steps 5) (cost 5 + g5)
    copied limits #[] activeFrame [] (.call 96 :: code5) scratch 72 112 post
  have pointerLocal4 := pointerRule4 hlocal
  have pointers4 := pointerLocal4 copiedCredit call5
  have copyRule4 := wp_copy_pair cfg ((f5 + steps 5) + 6) (6 * cfg.regularOpCost + (cost 5 + g5))
    (after 4) limits #[] activeFrame []
    ([.local_get 0, .i32_const 72, .i32_binop .add,
      .local_get 0, .i32_const 112, .i32_binop .add] ++ (.call 96 :: code5))
    scratch mi memoryIndex copyMemory post
  have copyLocal4 := copyRule4 hlocal
  have copyEnv4 := copyLocal4 hinv.module_copy hinv.memory_index hinv.memory_copy hinv.copy_wf
  have copyBounds4 := copyEnv4 hinv.copy_high_read hinv.copy_span
  have copyCredit4 : (after 4).host.gas.Credits
      (10 * cfg.regularOpCost + (6 * cfg.regularOpCost + (cost 5 + g5))) := a4.mono (by dsimp [g4, op]; omega)
  have h4 := copyBounds4 copyCredit4 pointers4
  have copyGas4 : 10 * cfg.regularOpCost + (6 * cfg.regularOpCost + (cost 5 + g5)) = g4 := by
    dsimp [g4, op]
    exact ten_six _ _
  rw [copyGas4] at h4
  have call4 := hcalls.readSupply.wp f4 g4 code4 post c4 h4
  rw [hboundaries.supplyArgs] at call4
  have argRule3 := wp_pointers cfg (f4 + steps 4) (cost 4 + g4)
    (after 3) limits #[] activeFrame [] (.call 414 :: code4) scratch 16 32 post
  have argLocal3 := argRule3 hlocal
  have h3 := argLocal3 a3 call4
  have call3 := hcalls.unwrapState.wp f3 g3 code3 post c3 h3
  rw [hboundaries.unwrapArgs] at call3
  have argRule2 := wp_pointers cfg (f3 + steps 3) (cost 3 + g3)
    (after 2) limits #[] activeFrame [] (.call 155 :: code3) scratch 32 72 post
  have argLocal2 := argRule2 hlocal
  have h2 := argLocal2 a2 call3
  have call2 := hcalls.readState.wp f2 g2 code2 post c2 h2
  rw [hboundaries.stateArgs] at call2
  have argRule1 := wp_pointer cfg (f2 + steps 2) (cost 2 + g2)
    (after 1) limits #[] activeFrame [] (.call 219 :: code2) scratch 72 post
  have argLocal1 := argRule1 hlocal
  have h1 := argLocal1 a1 call2
  have call1 := hcalls.installInterface.wp f1 g1 code1 post c1 h1
  rw [hboundaries.interfaceArgs] at call1
  have argRule0 := wp_interface_arguments cfg (f1 + steps 1) (cost 1 + g1)
    (after 0) limits #[] activeFrame [] (.call 520 :: code1) post
  have h0 := argRule0 a0 call1
  have call0 := hcalls.panicHook.wp f0 g0 code0 post c0 h0
  have prologueNext : WP cfg (f0 + steps 0) (.next (atCode
      (setGlobal (paid initial cfg.regularOpCost 5) globalIndex (.i32 (sp - 144))) limits #[]
      {frame with locals := frame.locals.set! 0 (.i32 (sp - 144))} [] (.call 522 :: code0)))
      (cost 0 + g0) post := by
    simpa only [hboundaries.prologue, hinv.scratch_eq] using call0
  have prologueRule := wp_prologue cfg (f0 + steps 0) (cost 0 + g0) initial limits #[] frame []
    (.call 522 :: code0) mi globalIndex originalGlobal sp post
  have prologueEnv := prologueRule hinv.module_initial hinv.global_index hinv.global_initial hinv.original_sp
  have whole := prologueEnv initialCredit prologueNext
  have hfuel : (f0 + steps 0) + 5 = fuel + bodySteps steps := by
    dsimp [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    exact bodyFuel_decomposition fuel steps
  rw [hfuel, hbudget] at whole
  simpa only [code0, code1, code2, code3, code4, code5, code6, code7, code8, code9, code10,
    WNear.Binary.TotalSupply.body, List.cons_append, List.nil_append, List.append_assoc] using whole

/-- Residual credits at the concrete restored store follow from the same
initial budget and local callee credit clauses; no execution premise is needed. -/
theorem final_credits (cfg : WasmConfig) (rest : Nat) (initial final : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (scratch pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (copyMemory : Memory)
    (hcalls : CallObligations cfg limits frame scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg initial final before after scratch globalIndex memoryIndex copyMemory)
    (hc : initial.host.gas.Credits (bodyCost cfg cost + rest)) : final.host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let g10 := 4 * op + rest
  let g9 := 3 * op + (cost 10 + g10)
  let g8 := 3 * op + (cost 9 + g9)
  let g7 := 4 * op + (cost 8 + g8)
  let g6 := 6 * op + (cost 7 + g7)
  let g5 := 7 * op + (cost 6 + g6)
  let g4 := 16 * op + (cost 5 + g5)
  let g3 := 6 * op + (cost 4 + g4)
  let g2 := 6 * op + (cost 3 + g3)
  let g1 := 3 * op + (cost 2 + g2)
  let g0 := 2 * op + (cost 1 + g1)
  have hbudget : 5 * op + (cost 0 + g0) = bodyCost cfg cost + rest := by
    clear hcalls hboundaries hc
    simp only [bodyCost, eleven_sum]
    dsimp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, op]
    omega
  have initialCredit : initial.host.gas.Credits (5 * op + (cost 0 + g0)) := by
    rw [hbudget]; exact hc
  have c0 : (before 0).host.gas.Credits (cost 0 + g0) := by
    rw [hboundaries.prologue]
    apply paid_credits
    exact initialCredit
  have a0 := hcalls.panicHook.credits g0 c0
  have c1 : (before 1).host.gas.Credits (cost 1 + g1) := by
    rw [hboundaries.interfaceArgs]
    apply paid_credits
    exact a0.mono (by dsimp [g0]; omega)
  have a1 := hcalls.installInterface.credits g1 c1
  have c2 : (before 2).host.gas.Credits (cost 2 + g2) := by
    rw [hboundaries.stateArgs]
    apply paid_credits
    exact a1.mono (by dsimp [g1]; omega)
  have a2 := hcalls.readState.credits g2 c2
  have c3 : (before 3).host.gas.Credits (cost 3 + g3) := by
    rw [hboundaries.unwrapArgs]
    apply paid_credits
    apply paid_credits
    exact a2.mono (by dsimp [g2]; omega)
  have a3 := hcalls.unwrapState.credits g3 c3
  have c4 : (before 4).host.gas.Credits (cost 4 + g4) := by
    rw [hboundaries.supplyArgs]
    apply paid_credits
    apply paid_credits
    exact a3.mono (by dsimp [g3]; omega)
  have a4 := hcalls.readSupply.credits g4 c4
  have c5 : (before 5).host.gas.Credits (cost 5 + g5) := by
    rw [hboundaries.serializeArgs]
    apply paid_credits
    apply paid_credits
    apply copyStore_credits
    exact a4.mono (by dsimp [g4]; omega)
  have a5 := hcalls.serialize.credits g5 c5
  have c6 : (before 6).host.gas.Credits (cost 6 + g6) := by
    rw [hboundaries.expectArgs]
    apply WNear.Proofs.StorePair.charged_credits
    apply paid_credits
    apply paid_credits
    exact a5.mono (by dsimp [g5]; omega)
  have a6 := hcalls.expectSerialization.credits g6 c6
  have c7 : (before 7).host.gas.Credits (cost 7 + g7) := by
    rw [hboundaries.sliceArgs]
    apply paid_credits
    apply paid_credits
    exact a6.mono (by dsimp [g6]; omega)
  have a7 := hcalls.vectorSlice.credits g7 c7
  have c8 : (before 8).host.gas.Credits (cost 8 + g8) := by
    rw [hboundaries.returnArgs]
    apply paid_credits
    exact a7.mono (by dsimp [g7]; omega)
  have a8 := hcalls.returnValue.credits g8 c8
  have c9 : (before 9).host.gas.Credits (cost 9 + g9) := by
    rw [hboundaries.dropReturnArgs]
    apply paid_credits
    exact a8.mono (by dsimp [g8]; omega)
  have a9 := hcalls.dropReturnVector.credits g9 c9
  have c10 : (before 10).host.gas.Credits (cost 10 + g10) := by
    rw [hboundaries.dropStateArgs]
    apply paid_credits
    exact a9.mono (by dsimp [g9]; omega)
  have a10 := hcalls.dropStateVector.credits g10 c10
  rw [hboundaries.restored]
  apply paid_credits
  exact a10

/-- The actual root frame returns void after the complete body and its final
free leave. Callee proofs remain exactly the named local obligations. -/
theorem wp_return (cfg : WasmConfig) (rest : Nat) (initial final : Store NearState)
    (limits : ExecLimits) (inst : Nat) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hcalls : CallObligations cfg limits (voidFrame #[.i32 scratch] inst)
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg initial final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants initial after (voidFrame #[.i32 0] inst) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hc : initial.host.gas.Credits (bodyCost cfg cost + rest)) :
    WP cfg (1 + bodySteps steps) (.next (atCode initial limits #[] (voidFrame #[.i32 0] inst) []
      WNear.Binary.TotalSupply.body)) (bodyCost cfg cost + rest)
      (fun remaining outcome error => remaining = rest ∧ outcome = .done [] final ∧ error = none) := by
  let post : Post := fun remaining outcome error => remaining = rest ∧ outcome = .done [] final ∧ error = none
  have hfinal := final_credits cfg rest initial final limits (voidFrame #[.i32 scratch] inst)
    before after cost steps scratch pointer length globalIndex memoryIndex copyMemory hcalls hboundaries hc
  have finish := wp_finish_void cfg 0 rest final limits #[.i32 scratch] inst post hfinal ⟨rfl, rfl, rfl⟩
  have hcalls' : CallObligations cfg limits
      {voidFrame #[.i32 0] inst with locals := #[.i32 0].set! 0 (.i32 scratch)}
      scratch pointer length before after cost steps := by
    simpa [voidFrame, Array.set!] using hcalls
  have continuation : WP cfg 1 (.next (atCode final limits #[]
      {voidFrame #[.i32 0] inst with locals := #[.i32 0].set! 0 (.i32 scratch)} [] [])) rest post := by
    simpa [voidFrame, Array.set!] using finish
  have rule := wp_body cfg 1 rest initial final limits (voidFrame #[.i32 0] inst) [] post
    before after cost steps mi globalIndex memoryIndex sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory
  have localCalls := rule hcalls' hboundaries hinv
  have result := localCalls hc continuation
  simpa only [List.append_nil] using result

/-- Actual metered execution of the root body returns the concrete final store.
The budget counts65pureopcodes and eleven complete local calls; the free root
leave adds one fuel step, while entry activation is separate. -/
theorem run_return (cfg : WasmConfig) (rest : Nat) (initial final : Store NearState)
    (limits : ExecLimits) (inst : Nat) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hcalls : CallObligations cfg limits (voidFrame #[.i32 scratch] inst)
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg initial final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants initial after (voidFrame #[.i32 0] inst) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hc : initial.host.gas.Credits (bodyCost cfg cost + rest)) :
    runMetered cfg (1 + bodySteps steps) (.next (atCode initial limits #[] (voidFrame #[.i32 0] inst) []
      WNear.Binary.TotalSupply.body)) = (.done [] final, none) := by
  have h := wp_return cfg rest initial final limits inst before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hcalls hboundaries hinv hc
  obtain ⟨_, hp, _⟩ := h.result
  exact Prod.ext hp.2.1 hp.2.2

end WNear.Proofs.TotalSupply
