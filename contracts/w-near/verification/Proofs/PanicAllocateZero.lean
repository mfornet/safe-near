import Binary.PanicAllocateZero
import Proofs.InterfaceSetBody
import Proofs.InterfaceInstall
import NearVM.MeteredLoopRules

/-! Actual zero-size f509 body and its typed local call. -/
namespace WNear.Proofs.PanicAllocateZero
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

/-- Sequential stores, retaining every byte outside the output record. -/
def zeroMemory (memory : Memory) (address : Nat) (alignment : UInt32) :=
  writeI32 (writeI32 memory (address + 4) 0) address alignment

def bodyStore (s : Store NearState) (op index : Nat) (out alignment : UInt32) (memory : Memory) :=
  InterfaceSetBody.twoWordsStore (paid s op 5) op index 4 0 out 0 alignment memory

def zeroFrame (frame : CallFrame) := {frame with locals := frame.locals.set! 1 (.i32 0)}

/-- The actual inner guard branches over all allocator and failure calls. -/
theorem wp_zero_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (post : Post) (hzero : frame.locals[1]? = some (.i32 0))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.PanicAllocateZero.zeroGuard ++ WNear.Binary.PanicAllocateZero.allocator)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack (emptyBlockFrame frame stack.size code) callers _ 1 (.i32 0) post hzero (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack (emptyBlockFrame frame stack.size code) callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    WNear.Binary.PanicAllocateZero.allocator 1 post (by decide)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

theorem bodyStore_credits (s : Store NearState) (op index rest : Nat) (out alignment : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (11 * op + rest)) : (bodyStore s op index out alignment memory).host.gas.Credits rest := by
  have paid5 := paid_credits s op 5 (6 * op + rest) (hc.mono (by omega))
  exact InterfaceSetBody.twoWordsStore_credits (paid s op 5) op index 4 0 rest out 0 alignment memory paid5

/-- Complete accepted body: two real block entries, a taken zero branch,
local reset, outer fallthrough and both bounded sequential writes. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out alignment : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hzero : frame.locals[1]? = some (.i32 0))
    (halign : frame.locals[2]? = some (.i32 alignment)) (hsize : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hwf : memory.wf) (hb : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyStore s cfg.regularOpCost index out alignment memory) limits
      stack (zeroFrame frame) callers code)) rest post) :
    WP cfg (fuel + 14) (.next (atCode s limits stack frame callers
      (WNear.Binary.PanicAllocateZero.body ++ code))) (11 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let updated := zeroFrame frame
  let stores := WNear.Binary.PanicAllocateZero.stores ++ code
  let outer := emptyBlockFrame frame stack.size stores
  have ha : updated.locals[0]? = some (.i32 out) := by simpa [updated, zeroFrame] using hout
  have hz : updated.locals[1]? = some (.i32 0) := by simp [updated, zeroFrame, show 1 < frame.locals.size by omega]
  have hv : updated.locals[2]? = some (.i32 alignment) := by simpa [updated, zeroFrame] using halign
  have hm5 : (paid s op 5).modules[updated.inst]? = some mi := by simpa only [paid, chargedStore, updated, zeroFrame] using hm
  have hmem5 : (paid s op 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have spec := writeI32_spec memory (out.toNat + 4) 0 hwf (by omega)
  have bound2 : out.toNat + 0 + 4 ≤ (writeI32 memory (out.toNat + 4) 0).byteSize := by rw [spec.2.1]; omega
  have cp := paid_credits s op 5 (6 * op + rest) (hc.mono (by dsimp [op]; omega))
  have writeRule := InterfaceSetBody.wp_two_words cfg fuel rest (paid s op 5) limits stack updated callers code
    0 1 2 4 0 out 0 alignment mi index memory post ha hz hv hm5 hi hmem5 (by omega) bound2 cp
  have writeNext : WP cfg fuel (.next (atCode (InterfaceSetBody.twoWordsStore (paid s op 5) op index 4 0 out 0 alignment memory)
      limits stack updated callers code)) rest post := by simpa only [bodyStore, updated, op] using hnext
  have writes := writeRule writeNext
  have endRule := wp_end_label cfg (fuel + 6) (6 * op + rest) (paid s op 5) limits stack updated callers
    {arity := 0, height := stack.size, rest := stores, loop := none} post cp
  have endNext : WP cfg (fuel + 6) (.next (atCode (paid s op 5) limits stack updated callers stores)) (6 * op + rest) post := by
    simpa only [WNear.Binary.PanicAllocateZero.stores, stores, op] using writes
  have ended := endRule endNext
  have setRule := wp_local_set cfg (fuel + 7) (6 * op + rest) (paid s op 4) limits stack outer callers [] 1 (.i32 0) post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega)))
  have setNext : WP cfg (fuel + 7) (.next (atCode (paid s op 5) limits stack {outer with locals := outer.locals.set! 1 (.i32 0)} callers []))
      (6 * op + rest) post := by
    simpa only [outer, emptyBlockFrame, updated, zeroFrame] using ended
  have reset := setRule setNext
  have constRule := wp_i32_const cfg (fuel + 8) (7 * op + rest) (paid s op 3) limits stack outer callers [.local_set 1] 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega)))
  have constNext : WP cfg (fuel + 8) (.next (atCode (paid s op 4) limits (stack.push (.i32 0)) outer callers [.local_set 1]))
      (7 * op + rest) post := by
    rw [show cfg.regularOpCost + (6 * op + rest) = 7 * op + rest by dsimp [op]; omega] at reset
    exact reset
  have constant := constRule constNext
  have guardRule := wp_zero_guard cfg (fuel + 9) (8 * op + rest) s limits stack outer callers WNear.Binary.PanicAllocateZero.reset post hzero
    (hc.mono (by dsimp [op]; omega))
  have guardNext : WP cfg (fuel + 9) (.next (atCode (paid s op 3) limits stack outer callers WNear.Binary.PanicAllocateZero.reset)) (8 * op + rest) post := by
    rw [show cfg.regularOpCost + (7 * op + rest) = 8 * op + rest by dsimp [op]; omega] at constant
    exact constant
  have guarded := guardRule guardNext
  have innerRule := wp_block_empty cfg (fuel + 12) (11 * op + rest) s limits stack outer callers
    (WNear.Binary.PanicAllocateZero.zeroGuard ++ WNear.Binary.PanicAllocateZero.allocator) WNear.Binary.PanicAllocateZero.reset post hc
  have innerNext : WP cfg (fuel + 12) (.next (atCode s limits stack (emptyBlockFrame outer stack.size WNear.Binary.PanicAllocateZero.reset) callers
      (WNear.Binary.PanicAllocateZero.zeroGuard ++ WNear.Binary.PanicAllocateZero.allocator))) (11 * op + rest) post := by
    rw [show 3 * cfg.regularOpCost + (8 * op + rest) = 11 * op + rest by dsimp [op]; omega] at guarded
    simpa only [Nat.add_assoc, Nat.reduceAdd] using guarded
  have inner := innerRule innerNext
  have outerRule := wp_block_empty cfg (fuel + 13) (11 * op + rest) s limits stack frame callers
    (.block .empty (WNear.Binary.PanicAllocateZero.zeroGuard ++ WNear.Binary.PanicAllocateZero.allocator) :: WNear.Binary.PanicAllocateZero.reset) stores post hc
  have result := outerRule inner
  simpa only [WNear.Binary.PanicAllocateZero.body, WNear.Binary.PanicAllocateZero.reset, stores,
    List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

theorem bodyStore_gas (s : Store NearState) (op index rest : Nat) (out alignment : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (11 * op + rest)) :
    (bodyStore s op index out alignment memory).host.gas.burnt = s.host.gas.burnt + 11 * op ∧
    (bodyStore s op index out alignment memory).host.gas.promises = s.host.gas.promises := by
  have h5 := paid_gas s op 5 (6 * op + rest) (hc.mono (by omega))
  have c5 := paid_credits s op 5 (6 * op + rest) (hc.mono (by omega))
  have h3 := paid_gas (paid s op 5) op 3 (3 * op + rest) (c5.mono (by omega))
  have c3 := paid_credits (paid s op 5) op 3 (3 * op + rest) (c5.mono (by omega))
  have hlast := paid_gas (InterfaceSetBody.storeWord (paid s op 5) op index 4 out 0 memory) op 3 rest c3
  refine ⟨?_, hlast.2.trans (h3.2.trans h5.2)⟩
  change (paid (InterfaceSetBody.storeWord (paid s op 5) op index 4 out 0 memory) op 3).host.gas.burnt = _
  rw [hlast.1]
  change (paid (paid s op 5) op 3).host.gas.burnt + 3 * op = _
  rw [h3.1, h5.1]; omega

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def calledStore (s : Store NearState) (op index : Nat) (out alignment : UInt32) (memory : Memory) :=
  bodyStore (entered s op) op index out alignment memory

theorem calledStore_credits (s : Store NearState) (op index rest : Nat) (out alignment : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (22 * op + rest)) : (calledStore s op index out alignment memory).host.gas.Credits rest := by
  have hop := StorePair.charged_credits s op (10 * op + (11 * op + rest)) (hc.mono (by omega))
  have activation := StorePair.charged_credits (chargedStore s op) (10 * op) (11 * op + rest) hop
  exact bodyStore_credits (entered s op) op index rest out alignment memory activation

theorem calledStore_gas (s : Store NearState) (op index rest : Nat) (out alignment : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (22 * op + rest)) :
    (calledStore s op index out alignment memory).host.gas.burnt = s.host.gas.burnt + 22 * op ∧
    (calledStore s op index out alignment memory).host.gas.promises = s.host.gas.promises := by
  have hop := GasCounter.burn_credits s.host.gas op (21 * op + rest) (hc.mono (by omega))
  have activation := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (11 * op + rest) (hop.2.2.2.mono (by omega))
  have body := bodyStore_gas (entered s op) op index rest out alignment memory activation.2.2.2
  refine ⟨?_, body.2.trans (activation.2.2.1.trans hop.2.2.1)⟩
  have active : (entered s op).host.gas.burnt = s.host.gas.burnt + op + 10 * op :=
    activation.2.1.trans (by rw [show (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op from hop.2.1])
  change (bodyStore (entered s op) op index out alignment memory).host.gas.burnt = _
  rw [body.1, active]; omega

/-- Typed real f509 call with arbitrary alignment and allocator flag. Size zero
skips every allocation callee; only the original output span is needed. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out alignment flag : UInt32) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hfi : mi.funcAddrs[509]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.PanicAllocateZero.signature frame.inst WNear.Binary.PanicAllocateZero.function))
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hwf : memory.wf) (hb : out.toNat + 8 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (22 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledStore s cfg.regularOpCost index out alignment memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 16) (.next (atCode s limits (base ++ [Value.i32 out, .i32 0, .i32 alignment, .i32 flag]).toArray frame callers
      (.call 509 :: code))) (22 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let callee : CallFrame := {locals := #[.i32 out, .i32 0, .i32 alignment, .i32 flag], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have hop := StorePair.charged_credits s op (10 * op + (11 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (11 * op + rest) := StorePair.charged_credits (chargedStore s op) (10 * op) (11 * op + rest) hop
  have cf := calledStore_credits s op index rest out alignment memory hc
  have leaveRule := wp_leave_wasm cfg fuel rest (calledStore s op index out alignment memory) limits base [] (zeroFrame callee) saved callers post rfl rfl rfl cf
  simp only [List.append_nil] at leaveRule
  have leaveNext : WP cfg fuel (.next (atCode (calledStore s op index out alignment memory) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have leaving := leaveRule leaveNext
  have module : active.modules[callee.inst]? = some mi := by simpa only [active, entered, chargedStore, callee] using hm
  have mem : active.mems[index]? = some memory := by simpa only [active, entered, chargedStore] using hmem
  have bodyRule := wp_body cfg (fuel + 1) rest active limits base.toArray callee (saved :: callers) [] out alignment mi index memory post
    rfl rfl rfl (by simp [callee]) module hi mem hwf hb ca
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (bodyStore active op index out alignment memory) limits base.toArray (zeroFrame callee) (saved :: callers) [])) rest post := by
    simpa only [calledStore, active, op] using leaving
  have body := bodyRule bodyNext
  have activation : activationGas op (wasmLocals WNear.Binary.PanicAllocateZero.function [.i32 out, .i32 0, .i32 alignment, .i32 flag]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.PanicAllocateZero.function, activationGas]
  have callRule := wp_call_wasm cfg ((fuel + 1) + 14) (11 * op + rest) s limits base [.i32 out, .i32 0, .i32 alignment, .i32 flag] frame callers code
    509 address mi WNear.Binary.PanicAllocateZero.signature frame.inst WNear.Binary.PanicAllocateZero.function post hm hfi hf rfl hdepth
  rw [activation] at callRule
  have next : WP cfg ((fuel + 1) + 14) (.next (wasmCallee active limits base frame callers code WNear.Binary.PanicAllocateZero.signature frame.inst
      WNear.Binary.PanicAllocateZero.function [.i32 out, .i32 0, .i32 alignment, .i32 flag])) (11 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.PanicAllocateZero.function, WNear.Binary.PanicAllocateZero.signature,
      atCode, callee, saved, List.map_nil, List.append_nil, Array.append_empty, List.length_cons, List.length_nil, Nat.reduceAdd, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (10 * op + (11 * op + rest)) = 22 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

/-- Exact words, byte footprint, well-formedness, size and limit of the result. -/
theorem zeroMemory_spec (memory : Memory) (address : Nat) (alignment : UInt32)
    (hwf : memory.wf) (hb : address + 8 ≤ memory.byteSize) :
    (zeroMemory memory address alignment).wf ∧
    (zeroMemory memory address alignment).byteSize = memory.byteSize ∧
    (zeroMemory memory address alignment).max = memory.max ∧
    readI32 (zeroMemory memory address alignment) address = alignment ∧
    readI32 (zeroMemory memory address alignment) (address + 4) = 0 ∧
    ∀ j, (j < address ∨ address + 8 ≤ j) → (zeroMemory memory address alignment).read8 j = memory.read8 j := by
  simpa only [zeroMemory, InterfaceInstall.installMemory] using InterfaceInstall.installMemory_spec memory address alignment 0 hwf hb

theorem calledStore_memory (s : Store NearState) (op index : Nat) (out alignment : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (calledStore s op index out alignment memory).mems[index]? = some (zeroMemory memory out.toNat alignment) := by
  let before := paid (entered s op) op 5
  have initial : before.mems[index]? = some memory := by simpa only [before, entered, paid, chargedStore] using hm
  have paidBefore : (paid before op 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using initial
  have first := storeI32_memory (paid before op 3) index (out.toNat + 4) memory 0 paidBefore
  have second : (paid (InterfaceSetBody.storeWord before op index 4 out 0 memory) op 3).mems[index]? = some (writeI32 memory (out.toNat + 4) 0) := by
    simpa only [InterfaceSetBody.storeWord, paid, chargedStore] using first
  have result := storeI32_memory (paid (InterfaceSetBody.storeWord before op index 4 out 0 memory) op 3) index out.toNat (writeI32 memory (out.toNat + 4) 0) alignment second
  simpa only [calledStore, bodyStore, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord, before, Nat.add_zero, zeroMemory] using result

theorem calledStore_resources (s : Store NearState) (op index : Nat) (out alignment : UInt32) (memory : Memory) :
    {calledStore s op index out alignment memory with mems := s.mems, host := s.host} = s := by
  simp only [calledStore, bodyStore, entered, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord, paid, chargedStore, storeI32]

theorem calledStore_host (s : Store NearState) (op index : Nat) (out alignment : UInt32) (memory : Memory) :
    {(calledStore s op index out alignment memory).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [calledStore, bodyStore, entered, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord, paid, chargedStore, storeI32_host, chargeHost]

end WNear.Proofs.PanicAllocateZero
