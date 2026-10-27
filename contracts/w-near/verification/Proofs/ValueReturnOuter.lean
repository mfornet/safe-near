import Binary.ValueReturnOuter
import Proofs.ValueReturnBorrowCounters
import Proofs.ValueReturnDispatch
import NearVM.MeteredSelectionRules
import NearVM.MeteredLoopRules

/-! Actual outer return-path pieces. Local adapters execute deployed code and
return to arbitrary saved callers; there are no guest-execution callbacks. -/
namespace WNear.Proofs.ValueReturnOuter
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def nonnullEntry (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def nonnullAfter (s : Store NearState) (op : Nat) := paid (nonnullEntry s op) op 3

theorem nonnullAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (13 * op + rest)) : (nonnullAfter s op).host.gas.Credits rest := by
  apply paid_credits
  apply WNear.Proofs.StorePair.charged_credits
  apply WNear.Proofs.StorePair.charged_credits
  exact hc.mono (by omega)

/-- Real f430 local call, including its checked nonzero branch and free return. -/
theorem wp_call_nonnull (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (ptr location : UInt32) (address inst : Nat) (mi : ModuleInst) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (ha : mi.funcAddrs[430]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction))
    (hnonzero : ptr ≠ 0) (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (nonnullAfter s cfg.regularOpCost) limits
      (base ++ [Value.i32 ptr]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits (base ++ [Value.i32 ptr, .i32 location]).toArray
      frame callers (.call 430 :: code))) (13 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := nonnullEntry s op
  let leaf : CallFrame := {locals := #[.i32 ptr, .i32 location], inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have h0 : s.host.gas.Credits (op + (9 * op + (3 * op + rest))) := hc.mono (by dsimp [op]; omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 : active.host.gas.Credits (3 * op + rest) := WNear.Proofs.StorePair.charged_credits (chargedStore s op) _ _ h1
  have hfinal := nonnullAfter_credits s op rest hc
  have leaveRule := wp_leave_wasm cfg fuel rest (nonnullAfter s op) limits base [.i32 ptr] leaf saved callers post rfl rfl rfl hfinal
  have hleave : WP cfg (fuel + 1) (.next (atCode (nonnullAfter s op) limits (base.toArray.push (.i32 ptr)) leaf (saved :: callers) [])) rest post := by
    have hnext' : WP cfg fuel (.next (atCode (nonnullAfter s op) limits (base ++ [Value.i32 ptr]).toArray saved callers saved.code)) rest post := by
      simpa only [saved, atCode] using hnext
    simpa using leaveRule hnext'
  have bodyRule := ValueReturnBorrow.wp_nonnull cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] ptr post rfl hnonzero h2
  have hbody := bodyRule hleave
  have activation : activationGas op (wasmLocals WNear.Binary.ValueReturnBorrow.nonnullFunction [.i32 ptr, .i32 location]) = 9 * op := by
    simpa [wasmLocals, WNear.Binary.ValueReturnBorrow.nonnullFunction] using WNear.Binary.ValueReturnBorrow.nonnull_activation op ptr location
  have callRule := wp_call_wasm cfg ((fuel + 1) + 4) (3 * op + rest) s limits base [.i32 ptr, .i32 location]
    frame callers code 430 address mi WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction post hm ha hf rfl hdepth
  rw [activation] at callRule
  have callPaid := callRule h0
  have bodyNext : WP cfg ((fuel + 1) + 4) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction [.i32 ptr, .i32 location])) (3 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.ValueReturnBorrow.nonnullFunction,
      WNear.Binary.ValueReturnBorrow.nonnullSignature, leaf, saved, atCode, List.map_nil,
      List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd, Array.append_empty] using hbody
  have result := callPaid bodyNext
  have budget : cfg.regularOpCost + (9 * op + (3 * op + rest)) = 13 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [budget] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

def checkAfter (s : Store NearState) (op index : Nat) (sp : UInt32) :=
  ValueReturnBorrow.checkedStore (nonnullEntry s op) op index sp

theorem checkAfter_credits (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (22 * op + rest)) : (checkAfter s op index sp).host.gas.Credits rest := by
  apply (ValueReturnBorrow.checkedStore_gas (nonnullEntry s op) op index rest sp _).2.2
  apply WNear.Proofs.StorePair.charged_credits
  apply WNear.Proofs.StorePair.charged_credits
  exact hc.mono (by omega)

/-- Actual zero-status f433 call and its saved-caller return. -/
theorem wp_call_check (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address inst index : Nat) (callerModule calleeModule : ModuleInst)
    (global : GlobalInst) (sp : UInt32) (post : Post)
    (hm : s.modules[frame.inst]? = some callerModule) (ha : callerModule.funcAddrs[433]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.checkFunction))
    (hcm : s.modules[inst]? = some calleeModule) (hi : calleeModule.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (22 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (checkAfter s cfg.regularOpCost index sp) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits (base ++ [Value.i32 0]).toArray
      frame callers (.call 433 :: code))) (22 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := nonnullEntry s op
  let leaf : CallFrame := {locals := #[.i32 0, .i32 0], inst, arity := 0, height := base.length, labels := [], code := []}
  let finished := {leaf with locals := leaf.locals.set! 1 (.i32 (sp - 16))}
  let saved := {frame with code}
  have h0 : s.host.gas.Credits (op + (9 * op + (12 * op + rest))) := hc.mono (by dsimp [op]; omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 : active.host.gas.Credits (12 * op + rest) := WNear.Proofs.StorePair.charged_credits (chargedStore s op) _ _ h1
  have hfinal := checkAfter_credits s op index rest sp hc
  have leaveRule := wp_leave_wasm cfg fuel rest (checkAfter s op index sp) limits base [] finished saved callers post rfl rfl rfl hfinal
  have hleave : WP cfg (fuel + 1) (.next (atCode (checkAfter s op index sp) limits base.toArray finished (saved :: callers) [])) rest post := by
    have hnext' : WP cfg fuel (.next (atCode (checkAfter s op index sp) limits base.toArray saved callers saved.code)) rest post := by
      simpa only [saved, atCode] using hnext
    simpa only [List.append_nil] using leaveRule (by simpa only [List.append_nil] using hnext')
  have hm' : active.modules[inst]? = some calleeModule := by simpa only [active, nonnullEntry, chargedStore] using hcm
  have hg' : active.globals[index]? = some global := by simpa only [active, nonnullEntry, chargedStore] using hg
  have bodyRule := ValueReturnBorrow.wp_check cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] calleeModule index global sp post
  have bodyShape := bodyRule rfl (by simp [leaf])
  have bodyEnv := bodyShape hm' hi hg' hsp
  have bodyPaid := bodyEnv h2
  have hbody := bodyPaid hleave
  have activation : activationGas op (wasmLocals WNear.Binary.ValueReturnBorrow.checkFunction [.i32 0]) = 9 * op := by
    simp [wasmLocals, WNear.Binary.ValueReturnBorrow.checkFunction, activationGas, ValType.default]
  have callRule := wp_call_wasm cfg ((fuel + 1) + 13) (12 * op + rest) s limits base [.i32 0]
    frame callers code 433 address callerModule WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.checkFunction post hm ha hf rfl hdepth
  rw [activation] at callRule
  have callPaid := callRule h0
  have bodyNext : WP cfg ((fuel + 1) + 13) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.checkFunction [.i32 0])) (12 * op + rest) post := by
    have locals_eq : wasmLocals WNear.Binary.ValueReturnBorrow.checkFunction [.i32 0] = #[.i32 0, .i32 0] := rfl
    simp only [wasmCallee]
    rw [locals_eq]
    simpa only [WNear.Binary.ValueReturnBorrow.checkFunction,
      WNear.Binary.ValueReturnBorrow.voidSignature, leaf, saved, atCode, List.length_nil, List.append_nil] using hbody
  have result := callPaid bodyNext
  have budget : cfg.regularOpCost + (9 * op + (12 * op + rest)) = 22 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [budget] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

def releaseAfter (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  ValueReturnBorrowCounters.releasedStore (nonnullEntry s op) op index counter memory

theorem releaseAfter_credits (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (36 * op + rest)) : (releaseAfter s op index counter memory).host.gas.Credits rest := by
  apply (ValueReturnBorrowCounters.releasedStore_gas (nonnullEntry s op) op index rest counter memory _).2.2
  apply WNear.Proofs.StorePair.charged_credits
  apply WNear.Proofs.StorePair.charged_credits
  exact hc.mono (by omega)

/-- Actual f431 call: follows its stored counter pointer, executes f672's swap,
and returns after discarding the previous counter. -/
theorem wp_call_release (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (record counter : UInt32) (address inst swapAddress swapInst index : Nat)
    (callerModule releaseModule swapModule : ModuleInst) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some callerModule) (ha : callerModule.funcAddrs[431]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction))
    (hcm : s.modules[inst]? = some releaseModule) (hi : releaseModule.memAddrs[0]? = some index)
    (hsa : releaseModule.funcAddrs[672]? = some swapAddress)
    (hsf : s.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature swapInst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hsm : s.modules[swapInst]? = some swapModule) (hsi : swapModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hcounter : readI32 memory record.toNat = counter)
    (hrb : record.toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (36 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (releaseAfter s cfg.regularOpCost index counter memory) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 19) (.next (atCode s limits (base ++ [Value.i32 record]).toArray
      frame callers (.call 431 :: code))) (36 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := nonnullEntry s op
  let leaf : CallFrame := {locals := #[.i32 record], inst, arity := 0, height := base.length, labels := [], code := []}
  let finished := ValueReturnBorrowCounters.releaseFrame leaf counter
  let saved := {frame with code}
  have h0 : s.host.gas.Credits (op + (9 * op + (26 * op + rest))) := hc.mono (by dsimp [op]; omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 : active.host.gas.Credits (26 * op + rest) := WNear.Proofs.StorePair.charged_credits (chargedStore s op) _ _ h1
  have hfinal := releaseAfter_credits s op index rest counter memory hc
  have leaveRule := wp_leave_wasm cfg fuel rest (releaseAfter s op index counter memory) limits base [] finished saved callers post rfl rfl rfl hfinal
  simp only [List.append_nil] at leaveRule
  have hleave : WP cfg (fuel + 1) (.next (atCode (releaseAfter s op index counter memory) limits base.toArray finished (saved :: callers) [])) rest post := by
    apply leaveRule
    simpa only [saved, atCode] using hnext
  have hm' : active.modules[inst]? = some releaseModule := by simpa only [active, nonnullEntry, chargedStore] using hcm
  have hf' : active.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature swapInst WNear.Binary.ValueReturnBorrow.swapFunction) := by
    simpa only [active, nonnullEntry, chargedStore] using hsf
  have hsm' : active.modules[swapInst]? = some swapModule := by simpa only [active, nonnullEntry, chargedStore] using hsm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, nonnullEntry, chargedStore] using hmem
  have nestedDepth : (saved :: callers).length + 1 < limits.maxCallDepth := by simp only [List.length_cons]; omega
  have bodyRule := ValueReturnBorrowCounters.wp_release cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] record counter
    releaseModule swapModule swapAddress swapInst index memory post
  have bodyShape := bodyRule rfl (by simp [leaf])
  have bodyEnv := bodyShape hcounter hm' hi hsa hf' hsm' hsi hmem' hrb hcb nestedDepth
  have bodyPaid := bodyEnv h2
  have hbody := bodyPaid hleave
  have activation : activationGas op (wasmLocals WNear.Binary.ValueReturnBorrow.releaseFunction [.i32 record]) = 9 * op := by
    simpa [wasmLocals, WNear.Binary.ValueReturnBorrow.releaseFunction] using WNear.Binary.ValueReturnBorrow.release_activation op record
  have depth : callers.length + 1 < limits.maxCallDepth := by omega
  have callRule := wp_call_wasm cfg ((fuel + 1) + 17) (26 * op + rest) s limits base [.i32 record]
    frame callers code 431 address callerModule WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction post hm ha hf rfl depth
  rw [activation] at callRule
  have callPaid := callRule h0
  have bodyNext : WP cfg ((fuel + 1) + 17) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction [.i32 record])) (26 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.ValueReturnBorrow.releaseFunction,
      WNear.Binary.ValueReturnBorrow.voidSignature, leaf, saved, atCode, List.map_nil,
      List.append_nil, List.length_nil, Array.append_empty] using hbody
  have result := callPaid bodyNext
  have budget : cfg.regularOpCost + (9 * op + (26 * op + rest)) = 36 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [budget] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

/-- The first actual borrow-record copy uses the old source word and writes
scratch+12. No disjointness premise is needed. -/
theorem wp_copy_record_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[2]? = some (.i32 scratch)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI32 (paid s cfg.regularOpCost 4) index (scratch.toNat + 12) memory (readI32 memory (scratch.toNat + 4)))
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.local_get 2, .local_get 2, .load .i32 none {align := 2, offset := 4},
        .store .i32 none {align := 2, offset := 12}] ++ code))) (4 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ 2 (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 2 (.i32 scratch) post hl
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := 4} scratch mi index memory post hm2 hi hmem2 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    {align := 2, offset := 12} scratch (readI32 memory (scratch.toNat + 4)) mi index memory post hm3 hi hmem3 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

/-- The second copy saves its loaded pointer in local3 before writing scratch+8. -/
theorem wp_copy_record_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[2]? = some (.i32 scratch)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 12 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (storeI32 (paid s cfg.regularOpCost 5) index (scratch.toNat + 8) memory (readI32 memory scratch.toNat))
      limits stack {frame with locals := frame.locals.set! 3 (.i32 (readI32 memory scratch.toNat))} callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get 2, .local_get 2, .load .i32 none {align := 2, offset := 0},
        .local_tee 3, .store .i32 none {align := 2, offset := 8}] ++ code))) (5 * cfg.regularOpCost + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s cfg.regularOpCost 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ 2 (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 2 (.i32 scratch) post hl
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits _ frame callers _
    {align := 2, offset := 0} scratch mi index memory post hm2 hi hmem2 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 3 (.i32 (readI32 memory scratch.toNat)) post
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 4) limits stack
    {frame with locals := frame.locals.set! 3 (.i32 (readI32 memory scratch.toNat))} callers code
    {align := 2, offset := 8} scratch (readI32 memory scratch.toNat) mi index memory post hm4 hi hmem4 (by dsimp only; omega)
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

/-- Actual pointer selection preceding f430. The loaded counter decides
whether the borrowed pointer or zero is passed to the nonnull checker. -/
theorem wp_select_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (ptr : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[3]? = some (.i32 ptr)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : ptr.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((stack.push (.i32 (if readI32 memory ptr.toNat ≠ 0 then ptr else 0))).push (.i32 1056164))
      frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      ([.local_get 3, .i32_const 0, .local_get 3, .load .i32 none {align := 2, offset := 0},
        .select none, .i32_const 1056164] ++ code))) (6 * cfg.regularOpCost + rest) post := by
  have hm3 : (paid s cfg.regularOpCost 3).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem3 : (paid s cfg.regularOpCost 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hconst := wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 5) limits
    (stack.push (.i32 (if readI32 memory ptr.toNat ≠ 0 then ptr else 0))) frame callers code 1056164 post
    (paid_credits s cfg.regularOpCost 5 (cfg.regularOpCost + rest) (hc.mono (by omega))) hnext
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack frame callers _ 3 (.i32 ptr) post hl (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 4) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ 3 (.i32 ptr) post hl
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 3) limits _ frame callers _
    {align := 2, offset := 0} ptr mi index memory post hm3 hi hmem3 (by simpa using hb)
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_select cfg (fuel + 1) _ (paid s cfg.regularOpCost 4) limits stack frame callers _
    (.i32 ptr) (.i32 0) (readI32 memory ptr.toNat) post
  · apply paid_credits; exact hc.mono (by omega)
  · have selected : (if readI32 memory ptr.toNat ≠ 0 then Value.i32 ptr else .i32 0) = .i32 (if readI32 memory ptr.toNat ≠ 0 then ptr else 0) := by split <;> rfl
    simpa only [selected, List.append, paid] using hconst

/-- Actual encoded cleanup-record argument. The bitwise-or is retained exactly;
no alignment premise silently replaces it with addition. -/
theorem wp_cleanup_argument (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (post : Post)
    (hl : frame.locals[2]? = some (.i32 scratch))
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (stack.push (.i32 ((scratch + 8) ||| 4))) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      ([.local_get 2, .i32_const 8, .i32_binop .add, .i32_const 4, .i32_binop .or] ++ code)))
      (5 * cfg.regularOpCost + rest) post := by
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ 2 (.i32 scratch) post hl (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 8 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ scratch 8 post
  · apply paid_credits; exact hc.mono (by omega)
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 3) limits _ frame callers _ 4 post
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_or cfg fuel rest (paid s cfg.regularOpCost 4) limits stack frame callers code (scratch + 8) 4 post
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

/-- The actual nonzero-cell guard preserves both enclosing labels. -/
theorem wp_cell_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (post : Post) (hn : cell ≠ 0)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      {frame with locals := frame.locals.set! 0 (.i32 cell)} callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits (stack.push (.i32 cell)) frame callers
      ([.local_tee 0, .i32_eqz, .br_if 0] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  have zero : Numeric.bool (cell == 0) = 0 := by simp [Numeric.bool, hn]
  have hbranch := wp_br_if_zero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack
    {frame with locals := frame.locals.set! 0 (.i32 cell)} callers code 0 post
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hnext
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 cell) post (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack _ callers _ cell post
  · apply paid_credits; exact hc.mono (by omega)
  · simpa only [zero, paid, List.append] using hbranch

/-- The actual two instructions selecting the success status. -/
theorem wp_success_status (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (post : Post)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack
      {frame with locals := frame.locals.set! 0 (.i32 0)} callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers ([.i32_const 0, .local_set 0] ++ code)))
      (2 * cfg.regularOpCost + rest) post := by
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ s limits stack frame callers _ 0 post (hc.mono (by omega))
  apply wp_local_set cfg fuel rest (paid s cfg.regularOpCost 1) limits stack frame callers code 0 (.i32 0) post
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

def epilogueAfter (s : Store NearState) (op globalIndex : Nat) (scratch : UInt32) :=
  setGlobal (paid (checkAfter (paid s op 1) op globalIndex scratch) op 4) globalIndex (.i32 (scratch + 16))

/-- Complete deployed f456 epilogue: real zero-status f433 call followed by
restoration of the caller's shadow-stack pointer. -/
theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch : UInt32) (mi : ModuleInst) (address index : Nat)
    (global : GlobalInst) (post : Post)
    (hstatus : frame.locals[0]? = some (.i32 0)) (hscratch : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (ha : mi.funcAddrs[433]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.checkFunction))
    (hi : mi.globalAddrs[0]? = some index) (hg : s.globals[index]? = some global)
    (hsp : global.value = .i32 scratch) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (27 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (epilogueAfter s cfg.regularOpCost index scratch) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 20) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnOuter.epilogue ++ code))) (27 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let arg := paid s op 1
  let checked := checkAfter arg op index scratch
  have carg : arg.host.gas.Credits (22 * op + (4 * op + rest)) := paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  have cchecked : checked.host.gas.Credits (4 * op + rest) := checkAfter_credits arg op index _ scratch carg
  have hmarg : arg.modules[frame.inst]? = some mi := by simpa only [arg, paid, chargedStore] using hm
  have hfarg : arg.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.checkFunction) := by
    simpa only [arg, paid, chargedStore] using hf
  have hgarg : arg.globals[index]? = some global := by simpa only [arg, paid, chargedStore] using hg
  have hmchecked : checked.modules[frame.inst]? = some mi := by
    simpa only [checked, checkAfter, nonnullEntry, ValueReturnBorrow.checkedStore, paid, chargedStore, setGlobal] using hmarg
  have hglobals : checked.globals = arg.globals := by
    exact ValueReturnBorrow.checkedStore_globals (nonnullEntry arg op) op index scratch global hgarg hsp
  have hgchecked : checked.globals[index]? = some global := by rw [hglobals]; exact hgarg
  have hrestore := ValueReturnBorrow.wp_restore cfg fuel rest checked limits base.toArray frame callers code mi index global scratch 2 post
    hscratch hmchecked hi hgchecked cchecked hnext
  have callRule := wp_call_check cfg (fuel + 4) (4 * op + rest) arg limits base frame callers
    (WNear.Binary.ValueReturnBorrow.checkEpilogue.map (fun i => match i with | .local_get 1 => .local_get 2 | _ => i) ++ code)
    address frame.inst index mi mi global scratch post hmarg ha hfarg hmarg hi hgarg hsp hd carg
  have callNext : WP cfg (fuel + 4) (.next (atCode checked limits base.toArray frame callers
      (WNear.Binary.ValueReturnBorrow.checkEpilogue.map (fun i => match i with | .local_get 1 => .local_get 2 | _ => i) ++ code))) (4 * op + rest) post := by
    simpa only [WNear.Binary.ValueReturnBorrow.checkEpilogue, List.map_cons, List.map_nil, List.append] using hrestore
  have called := callRule callNext
  rw [show 27 * cfg.regularOpCost + rest = cfg.regularOpCost + (22 * op + (4 * op + rest)) by dsimp [op]; omega]
  have getRule := wp_local_get cfg ((fuel + 4) + 15) (22 * op + (4 * op + rest)) s limits base.toArray frame callers (.call 433 :: [.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code) 0 (.i32 0) post hstatus (hc.mono (by dsimp [op]; omega))
  have hcalled : WP cfg ((fuel + 4) + 15) (.next (atCode arg limits (base.toArray.push (.i32 0)) frame callers
      (.call 433 :: [.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0] ++ code))) (22 * op + (4 * op + rest)) post := by
    simpa [WNear.Binary.ValueReturnBorrow.checkEpilogue] using called
  have result := getRule hcalled
  simpa only [WNear.Binary.ValueReturnOuter.epilogue, List.append, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

theorem wp_lookup_argument (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (interface : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hl : frame.locals[0]? = some (.i32 interface)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : interface.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits
      (stack.push (.i32 (readI32 memory interface.toNat))) frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers
      ([.local_get 0, .load .i32 none {align := 2, offset := 0}] ++ code))) (2 * cfg.regularOpCost + rest) post := by
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ s limits stack frame callers _ 0 (.i32 interface) post hl (hc.mono (by omega))
  apply wp_i32_load cfg fuel rest (paid s cfg.regularOpCost 1) limits stack frame callers code
    {align := 2, offset := 0} interface mi index memory post hm1 hi hmem1 (by simpa using hb)
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

theorem wp_acquire_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch cell : UInt32) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hc0 : frame.locals[0]? = some (.i32 cell))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (((stack.push (.i32 scratch)).push (.i32 cell)).push (.i32 1056148)) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 2, .local_get 0, .i32_const 1056148] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 2 (.i32 scratch) post hs (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 (.i32 cell) post hc0
  · apply paid_credits; exact hc.mono (by omega)
  apply wp_i32_const cfg fuel rest (paid s cfg.regularOpCost 2) limits _ frame callers code 1056148 post
  · apply paid_credits; exact hc.mono (by omega)
  · exact hnext

def cleanupAfter (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (scratch counter : UInt32) (memory : Memory) :=
  epilogueAfter (chargedStore (releaseAfter (paid s op 5) op memoryIndex counter memory) op) op globalIndex scratch

/-- The entire actual normal suffix after dispatch: encoded release argument,
f431/f672, br1 out of both blocks, f433 and SP restoration. -/
theorem wp_normal_cleanup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch counter : UInt32) (mi : ModuleInst)
    (releaseAddress swapAddress checkAddress globalIndex memoryIndex : Nat)
    (global : GlobalInst) (memory : Memory) (post : Post)
    (hstatus : frame.locals[0]? = some (.i32 0)) (hspLocal : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some memoryIndex)
    (hmem : s.mems[memoryIndex]? = some memory)
    (hra : mi.funcAddrs[431]? = some releaseAddress)
    (hrf : s.funcs[releaseAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.releaseFunction))
    (hsa : mi.funcAddrs[672]? = some swapAddress)
    (hsf : s.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hca : mi.funcAddrs[433]? = some checkAddress)
    (hcf : s.funcs[checkAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.checkFunction))
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hg : s.globals[globalIndex]? = some global)
    (hsp : global.value = .i32 scratch)
    (hcounter : readI32 memory (((scratch + 8) ||| 4).toNat) = counter)
    (hrb : ((scratch + 8) ||| 4).toNat + 4 ≤ memory.byteSize)
    (hcb : counter.toNat + 4 ≤ memory.byteSize) (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (69 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (cleanupAfter s cfg.regularOpCost globalIndex memoryIndex scratch counter memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 45) (.next (atCode s limits base.toArray
      (emptyBlockFrame (emptyBlockFrame frame base.toArray.size (WNear.Binary.ValueReturnOuter.epilogue ++ code))
        base.toArray.size WNear.Binary.ValueReturnOuter.fallback) callers WNear.Binary.ValueReturnOuter.cleanup))
      (69 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let arg := paid s op 5
  let released := releaseAfter arg op memoryIndex counter memory
  let branched := chargedStore released op
  let nested := emptyBlockFrame (emptyBlockFrame frame base.toArray.size (WNear.Binary.ValueReturnOuter.epilogue ++ code))
    base.toArray.size WNear.Binary.ValueReturnOuter.fallback
  have carg : arg.host.gas.Credits (36 * op + (op + (27 * op + rest))) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have creleased : released.host.gas.Credits (op + (27 * op + rest)) := releaseAfter_credits arg op memoryIndex _ counter memory carg
  have cbranched : branched.host.gas.Credits (27 * op + rest) := WNear.Proofs.StorePair.charged_credits released op _ creleased
  have hmarg : arg.modules[frame.inst]? = some mi := by simpa only [arg, paid, chargedStore] using hm
  have hrarg : arg.funcs[releaseAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.releaseFunction) := by simpa only [arg, paid, chargedStore] using hrf
  have hsarg : arg.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature frame.inst WNear.Binary.ValueReturnBorrow.swapFunction) := by simpa only [arg, paid, chargedStore] using hsf
  have hmemarg : arg.mems[memoryIndex]? = some memory := by simpa only [arg, paid, chargedStore] using hmem
  have hmb : branched.modules[frame.inst]? = some mi := by simpa only [branched, released, releaseAfter, arg, nonnullEntry, ValueReturnBorrowCounters.releasedStore, ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore, ValueReturnBorrowCounters.swapEntryStore, paid, chargedStore, storeI32] using hm
  have hfb : branched.funcs[checkAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature frame.inst WNear.Binary.ValueReturnBorrow.checkFunction) := by
    simpa only [branched, released, releaseAfter, arg, nonnullEntry, ValueReturnBorrowCounters.releasedStore, ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore, ValueReturnBorrowCounters.swapEntryStore, paid, chargedStore, storeI32] using hcf
  have hgb : branched.globals[globalIndex]? = some global := by simpa only [branched, released, releaseAfter, arg, nonnullEntry, ValueReturnBorrowCounters.releasedStore, ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore, ValueReturnBorrowCounters.swapEntryStore, paid, chargedStore, storeI32] using hg
  have epilogue := wp_epilogue cfg fuel rest branched limits base frame callers code scratch mi checkAddress globalIndex global post
    hstatus hspLocal hmb hca hfb hgi hgb hsp (by omega) cbranched hnext
  have branch := wp_br_two_blocks cfg (fuel + 20) (27 * op + rest) released limits base.toArray frame callers
    (WNear.Binary.ValueReturnOuter.epilogue ++ code) WNear.Binary.ValueReturnOuter.fallback [] post creleased epilogue
  have releaseRule := wp_call_release cfg ((fuel + 20) + 1) (op + (27 * op + rest)) arg limits base nested callers
    [.br 1] ((scratch + 8) ||| 4) counter releaseAddress frame.inst swapAddress frame.inst memoryIndex mi mi mi memory post
    hmarg hra hrarg hmarg hi hsa hsarg hmarg hi hmemarg hcounter hrb hcb hd carg
  have releaseNext : WP cfg ((fuel + 20) + 1) (.next (atCode released limits base.toArray nested callers [.br 1])) (op + (27 * op + rest)) post := by
    simpa only [nested] using branch
  have releaseProof := releaseRule releaseNext
  have releaseStack : (base ++ [Value.i32 ((scratch + 8) ||| 4)]).toArray = base.toArray.push (.i32 ((scratch + 8) ||| 4)) := by
    apply Array.toList_inj.mp; simp
  have argumentNext : WP cfg (((fuel + 20) + 1) + 19) (.next (atCode arg limits
      (base.toArray.push (.i32 ((scratch + 8) ||| 4))) nested callers [.call 431, .br 1])) (36 * op + (op + (27 * op + rest))) post := by
    simpa only [releaseStack] using releaseProof
  have argumentRule := wp_cleanup_argument cfg (((fuel + 20) + 1) + 19) (36 * op + (op + (27 * op + rest))) s limits base.toArray nested callers
    [.call 431, .br 1] scratch post hspLocal (hc.mono (by dsimp [op]; omega))
  have result := argumentRule argumentNext
  have budget : 5 * cfg.regularOpCost + (36 * op + (op + (27 * op + rest))) = 69 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [budget] at result
  simpa only [WNear.Binary.ValueReturnOuter.cleanup, List.append, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd, nested] using result

end WNear.Proofs.ValueReturnOuter
