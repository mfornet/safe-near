import Proofs.PanicHookState
import Proofs.PanicHookSet
import Proofs.PanicAllocatePointerCall

/-! Actual panic-hook setup body, composed from the zero-size allocation and
first-hook replacement calls. -/
namespace WNear.Proofs.PanicHookBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open PanicHookState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- The exact constant arguments of the deployed allocator call. -/
theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (post : Post)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits
      ((stack.push (.i32 0)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers
      ([.i32_const 0, .i32_const 1] ++ code))) (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  apply wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 1) limits (stack.push (.i32 0)) frame callers code 1 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  · exact hnext


/-- Real constant arguments and full zero-size503 call, returning pointerone
from its proved sequential508/509 memory operations. -/
theorem wp_allocate (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hr : Ready s limits frame.inst (callers.length + 1) p)
    (hc : s.host.gas.Credits (88 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (allocated s cfg.regularOpCost p) limits
      (base ++ [Value.i32 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 65) (.next (atCode s limits base.toArray frame callers
      ([.i32_const 0, .i32_const 1, .call 503] ++ code))) (88 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 2
  have resource := hr.paid s op 2 limits frame.inst (callers.length + 1) p
  have r0 := resource.charge prepared op limits frame.inst (callers.length + 1) p
  have r1 := r0.charge (chargedStore prepared op) (10 * op) limits frame.inst (callers.length + 1) p
  have pointer := r1.pointer_ready (allocationEntry prepared op) limits frame.inst (callers.length + 1) p base.length
    ({frame with code} :: callers) (by simp)
  have pointerReady : PanicAllocatePointerState.Ready (PanicAllocatePointerCall.entered prepared op) limits
      (PanicAllocatePointerCall.leaf frame.inst base.length) ({frame with code} :: callers) p := by
    simpa only [PanicAllocatePointerCall.entered, PanicAllocatePointerCall.leaf, pointerFrame, allocationEntry] using pointer
  have callRule := PanicAllocatePointerCall.wp_call cfg fuel rest prepared limits base frame callers code p 503 post resource.module resource.allocatorIndex resource.allocator
    pointerReady (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega)))
  have callNext : WP cfg fuel (.next (atCode (PanicAllocatePointerCall.callAfter prepared op p) limits
      (base ++ [Value.i32 1]).toArray frame callers code)) rest post := by
    simpa only [allocated, PanicAllocatePointerCall.callAfter, PanicAllocatePointerCall.entered, allocationEntry, prepared, op] using hnext
  have call := callRule callNext
  have callStack : WP cfg (fuel + 63) (.next (atCode prepared limits ((base.toArray.push (.i32 0)).push (.i32 1)) frame callers
      (.call 503 :: code))) (86 * op + rest) post := by simpa using call
  have result := wp_arguments cfg (fuel + 63) (86 * op + rest) s limits base.toArray frame callers (.call 503 :: code) post
    (hc.mono (by dsimp [op]; omega)) callStack
  rw [show 2 * cfg.regularOpCost + (86 * op + rest) = 88 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.cons_append, List.nil_append] using result

def hookAfter (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) :=
  PanicHookSet.after (hookEntry s op) op index memory receiver vtable

/-- Real typed822 invocation; the callee's explicit return restores the caller.
Only the original snapshot predicates select its first-install branch. -/
theorem wp_call_hook (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (memory : Memory) (receiver vtable : UInt32) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[822]? = some 822)
    (hf : s.funcs[822]? = some (.wasm WNear.Binary.PanicHookSet.signature frame.inst WNear.Binary.PanicHookSet.function))
    (hwf : memory.wf) (hb : 1074936 ≤ memory.byteSize)
    (hinit : readI32 memory 1074932 = 0) (hunlock : readI32 memory 1074920 = 0) (hold : readI32 memory 1074928 = 0)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (42 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (hookAfter s cfg.regularOpCost index memory receiver vtable) limits
      base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 36) (.next (atCode s limits (base ++ [Value.i32 receiver, .i32 vtable]).toArray frame callers
      (.call 822 :: code))) (42 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := hookEntry s op
  let leaf : CallFrame := {locals := #[.i32 receiver, .i32 vtable, .i32 0], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have module : active.modules[leaf.inst]? = some mi := by simpa only [active, hookEntry, chargedStore, leaf] using hm
  have mem : active.mems[index]? = some memory := by simpa only [active, hookEntry, chargedStore] using hmem
  have ready : PanicHookSet.Ready active leaf mi index memory receiver vtable :=
    ⟨module, hi, mem, rfl, rfl, by simp [leaf], hwf, hb, hinit, hunlock, hold⟩
  have hop := StorePair.charged_credits s op (10 * op + (31 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (31 * op + rest) := StorePair.charged_credits (chargedStore s op) (10 * op) (31 * op + rest) hop
  have bodyRule := PanicHookSet.wp_body cfg fuel rest active limits base leaf saved callers mi index memory receiver vtable post ready rfl rfl ca
  have bodyNext : WP cfg fuel (.next (atCode (PanicHookSet.after active op index memory receiver vtable) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [hookAfter, active, saved, atCode, op] using hnext
  have body := bodyRule bodyNext
  have callRule := wp_call_wasm cfg (fuel + 35) (31 * op + rest) s limits base [.i32 receiver, .i32 vtable] frame callers code
    822 822 mi WNear.Binary.PanicHookSet.signature frame.inst WNear.Binary.PanicHookSet.function post hm hfi hf rfl hd
  have activation : activationGas op (wasmLocals WNear.Binary.PanicHookSet.function [.i32 receiver, .i32 vtable]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.PanicHookSet.function, activationGas, ValType.default]
  rw [activation] at callRule
  have localsArray : #[Value.i32 receiver, .i32 vtable] ++ #[Value.i32 0] = #[Value.i32 receiver, .i32 vtable, .i32 0] := rfl
  have next : WP cfg (fuel + 35) (.next (wasmCallee active limits base frame callers code WNear.Binary.PanicHookSet.signature frame.inst
      WNear.Binary.PanicHookSet.function [.i32 receiver, .i32 vtable])) (31 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.PanicHookSet.function, WNear.Binary.PanicHookSet.signature, atCode,
      leaf, saved, List.map_cons, List.map_nil, List.append_cons, List.append_nil, ValType.default, localsArray,
      List.length_cons, List.length_nil, Nat.reduceAdd, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (10 * op + (31 * op + rest)) = 42 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

def hookTailAfter (s : Store NearState) (op index : Nat) (memory : Memory) (receiver : UInt32) :=
  hookAfter (paid s op 1) op index memory receiver 1055136

/-- Separately checked43-unit suffix, over an arbitrary current heap. -/
theorem wp_hook_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (memory : Memory) (receiver : UInt32) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hfi : mi.funcAddrs[822]? = some 822)
    (hf : s.funcs[822]? = some (.wasm WNear.Binary.PanicHookSet.signature frame.inst WNear.Binary.PanicHookSet.function))
    (hwf : memory.wf) (hb : 1074936 ≤ memory.byteSize)
    (hinit : readI32 memory 1074932 = 0) (hunlock : readI32 memory 1074920 = 0) (hold : readI32 memory 1074928 = 0)
    (hd : callers.length + 1 < limits.maxCallDepth) (hc : s.host.gas.Credits (43 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (hookTailAfter s cfg.regularOpCost index memory receiver) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 37) (.next (atCode s limits (base ++ [Value.i32 receiver]).toArray frame callers
      (.i32_const 1055136 :: .call 822 :: code))) (43 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let args := paid s op 1
  have module : args.modules[frame.inst]? = some mi := by simpa only [args, paid, chargedStore] using hm
  have mem : args.mems[index]? = some memory := by simpa only [args, paid, chargedStore] using hmem
  have function : args.funcs[822]? = some (.wasm WNear.Binary.PanicHookSet.signature frame.inst WNear.Binary.PanicHookSet.function) := by
    simpa only [args, paid, chargedStore] using hf
  have credits := paid_credits s op 1 (42 * op + rest) (hc.mono (by dsimp [op]; omega))
  have rule := wp_call_hook cfg fuel rest args limits base frame callers code mi index memory receiver 1055136 post
    module hi mem hfi function hwf hb hinit hunlock hold hd credits
  have next : WP cfg fuel (.next (atCode (hookAfter args op index memory receiver 1055136) limits base.toArray frame callers code)) rest post := by
    simpa only [hookTailAfter, args, op] using hnext
  have call := rule next
  have constRule := wp_i32_const cfg (fuel + 36) (42 * op + rest) s limits (base ++ [Value.i32 receiver]).toArray frame callers
    (.call 822 :: code) 1055136 post (hc.mono (by dsimp [op]; omega))
  have stack : WP cfg (fuel + 36) (.next (atCode args limits ((base ++ [Value.i32 receiver]).toArray.push (.i32 1055136)) frame callers
      (.call 822 :: code))) (42 * op + rest) post := by simpa using call
  have result := constRule stack
  rw [show cfg.regularOpCost + (42 * op + rest) = 43 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

/-- The complete deployed522 body executes both proved calls. The allocator's
pointerone and current heap follow from its actual writes. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hr : Ready s limits frame.inst (callers.length + 1) p)
    (hc : s.host.gas.Credits (131 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 102) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.PanicHook.body ++ code))) (131 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let alloc := allocated s op p
  let memory := PanicAllocatePointerState.finalMemory p
  have ca := allocated_credits s op (43 * op + rest) p (hc.mono (by dsimp [op]; omega))
  have fields := allocated_fields s op p
  have module : alloc.modules[frame.inst]? = some p.mi := by rw [fields.2.1]; exact hr.module
  have function : alloc.funcs[822]? = some (.wasm WNear.Binary.PanicHookSet.signature frame.inst WNear.Binary.PanicHookSet.function) := by
    rw [fields.1]; exact hr.hook
  have mem : alloc.mems[p.memoryIndex]? = some memory := allocated_memory s op p hr.memory
  have spec := PanicAllocatePointerBody.final_spec p hr.wf hr.width hr.spLower hr.stackBound
  have depth : callers.length + 1 < limits.maxCallDepth := by have hd := hr.depth; omega
  have tailRule := wp_hook_tail cfg fuel rest alloc limits base frame callers code p.mi p.memoryIndex memory 1 post
    module hr.memoryIndex mem hr.hookIndex function spec.1 hr.hookSpan hr.initial hr.unlocked hr.oldVtable depth ca
  have tailNext : WP cfg fuel (.next (atCode (hookTailAfter alloc op p.memoryIndex memory 1) limits base.toArray frame callers code)) rest post := by
    simpa only [after, hookTailAfter, hookAfter, alloc, memory, hookArguments, op] using hnext
  have tail := tailRule tailNext
  have allocationRule := wp_allocate cfg (fuel + 37) (43 * op + rest) s limits base frame callers
    (.i32_const 1055136 :: .call 822 :: code) p post hr (hc.mono (by dsimp [op]; omega))
  have result := allocationRule tail
  rw [show 88 * cfg.regularOpCost + (43 * op + rest) = 131 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.PanicHook.body, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

end WNear.Proofs.PanicHookBody
