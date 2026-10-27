import Proofs.ValueReturnBorrow
import NearVM.MeteredWasmCall
import NearVM.MeteredI32MemoryRules

/-! Actual counter swap and cleanup used by the deployed RefCell wrapper. -/
namespace WNear.Proofs.ValueReturnBorrowCounters
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def swapStore (s : Store NearState) (op index : Nat) (address value : UInt32)
    (memory : Memory) : Store NearState :=
  storeI32 (paid s op 7) index address.toNat memory value

def swapFrame (frame : CallFrame) (memory : Memory) (address : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 2 (.i32 (readI32 memory address.toNat))}

/-- The actual seven-opcode f672 swaps one bounded word. No memory separation
premise is needed; the returned value is read before the write. -/
theorem wp_swap (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (address value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (haddress : frame.locals[0]? = some (.i32 address))
    (hvalue : frame.locals[1]? = some (.i32 value)) (hsize : 3 ≤ frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : address.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (swapStore s cfg.regularOpCost index address value memory)
      limits (stack.push (.i32 (readI32 memory address.toNat))) (swapFrame frame memory address) callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnBorrow.swapBody ++ code))) (7 * cfg.regularOpCost + rest) post := by
  let frame' := swapFrame frame memory address
  have ha : frame'.locals[0]? = some (.i32 address) := by simpa [frame', swapFrame] using haddress
  have hv : frame'.locals[1]? = some (.i32 value) := by simpa [frame', swapFrame] using hvalue
  have ho : frame'.locals[2]? = some (.i32 (readI32 memory address.toNat)) := by
    simp [frame', swapFrame, show 2 < frame.locals.size by omega]
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by
    simpa only [paid, chargedStore] using hmodule
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by
    simpa only [paid, chargedStore] using hmemory
  have hm5 : (paid s cfg.regularOpCost 5).modules[frame'.inst]? = some mi := by
    simpa only [paid, chargedStore, frame', swapFrame] using hmodule
  have hmem5 : (paid s cfg.regularOpCost 5).mems[index]? = some memory := by
    simpa only [paid, chargedStore] using hmemory
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) _ s limits stack frame callers _ 0 (.i32 address) post haddress (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 5) _ (paid s cfg.regularOpCost 1) limits stack frame callers _
    {align := 2, offset := 0} address mi index memory post hm1 hindex hmem1 (by simpa using hbound)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_set cfg (fuel + 4) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ 2
    (.i32 (readI32 memory address.toNat)) post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 3) limits stack frame' callers _ 0 (.i32 address) post ha
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 4) limits _ frame' callers _ 1 (.i32 value) post hv
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_store cfg (fuel + 1) _ (paid s cfg.regularOpCost 5) limits stack frame' callers _
    {align := 2, offset := 0} address value mi index memory post hm5 hindex hmem5 (by simpa using hbound)
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  apply wp_local_get cfg fuel rest _ limits stack frame' callers code 2 (.i32 (readI32 memory address.toNat)) post ho
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  · exact hnext

theorem swapStore_credits (s : Store NearState) (op index rest : Nat) (address value : UInt32)
    (memory : Memory) (hc : s.host.gas.Credits (7 * op + rest)) :
    (swapStore s op index address value memory).host.gas.Credits rest :=
  paid_credits s op 7 rest hc

theorem swapStore_gas (s : Store NearState) (op index rest : Nat) (address value : UInt32)
    (memory : Memory) (hc : s.host.gas.Credits (7 * op + rest)) :
    (swapStore s op index address value memory).host.gas.burnt = s.host.gas.burnt + 7 * op ∧
    (swapStore s op index address value memory).host.gas.promises = s.host.gas.promises :=
  paid_gas s op 7 rest hc

theorem swapStore_resources (s : Store NearState) (op index : Nat) (address value : UInt32) (memory : Memory) :
    {swapStore s op index address value memory with host := s.host, mems := s.mems} = s := by
  simp only [swapStore, storeI32, paid, chargedStore]

/-- The exact four bytes and every outside byte are described by writeI32_spec. -/
theorem swapStore_memory (s : Store NearState) (op index : Nat) (address value : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (swapStore s op index address value memory).mems[index]? = some (writeI32 memory address.toNat value) := by
  apply storeI32_memory
  simpa only [paid, chargedStore] using hm

theorem wp_swap_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (address value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (ha : locals[0]? = some (.i32 address)) (hv : locals[1]? = some (.i32 value))
    (hs : 3 ≤ locals.size) (hm : s.modules[inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : address.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest)) :
    WP cfg 8 (.next (atCode s limits #[] (resultFrame locals inst) [] WNear.Binary.ValueReturnBorrow.swapBody))
      (7 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [.i32 (readI32 memory address.toNat)] (swapStore s cfg.regularOpCost index address value memory) ∧ error = none) := by
  have c := swapStore_credits s cfg.regularOpCost index rest address value memory hc
  have hf := wp_finish_i32 cfg 0 rest (swapStore s cfg.regularOpCost index address value memory) limits
    (locals.set! 2 (.i32 (readI32 memory address.toNat))) inst (readI32 memory address.toNat)
    (fun remaining final error => remaining = rest ∧
      final = .done [.i32 (readI32 memory address.toNat)] (swapStore s cfg.regularOpCost index address value memory) ∧ error = none) c ⟨rfl, rfl, rfl⟩
  have h := wp_swap cfg 1 rest s limits #[] (resultFrame locals inst) [] [] address value mi index memory
    (fun remaining final error => remaining = rest ∧
      final = .done [.i32 (readI32 memory address.toNat)] (swapStore s cfg.regularOpCost index address value memory) ∧ error = none)
    ha hv hs hm hi hmem hb hc
  apply h
  exact hf

def swapEntryStore (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (10 * op)

def calledSwapStore (s : Store NearState) (op index : Nat) (address value : UInt32)
    (memory : Memory) : Store NearState := swapStore (swapEntryStore s op) op index address value memory

theorem calledSwapStore_credits (s : Store NearState) (op index rest : Nat) (address value : UInt32)
    (memory : Memory) (hc : s.host.gas.Credits (18 * op + rest)) :
    (calledSwapStore s op index address value memory).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (17 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (7 * op + rest)
    (hop.2.2.2.mono (by omega))
  exact swapStore_credits (swapEntryStore s op) op index rest address value memory ha.2.2.2

/-- A real direct call to deployed f672, including callee activation and its
free return to the caller. Primitive loader and memory facts replace any
callee-execution assumption. -/
theorem wp_call_swap (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address value : UInt32) (callerModule calleeModule : ModuleInst)
    (functionAddress inst index : Nat) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some callerModule)
    (hfunctionIndex : callerModule.funcAddrs[672]? = some functionAddress)
    (hfunction : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcalleeModule : s.modules[inst]? = some calleeModule)
    (hindex : calleeModule.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : address.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (18 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (calledSwapStore s cfg.regularOpCost index address value memory) limits
      (base ++ [Value.i32 (readI32 memory address.toNat)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits (base ++ [Value.i32 address, .i32 value]).toArray
      frame callers (.call 672 :: code))) (18 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee : CallFrame :=
    {locals := #[.i32 address, .i32 value, .i32 0]
     inst := inst
     arity := 1
     height := base.length
     labels := []
     code := []}
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (17 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (7 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hm : (swapEntryStore s op).modules[inst]? = some calleeModule := by
    simpa only [swapEntryStore, chargedStore] using hcalleeModule
  have hmem : (swapEntryStore s op).mems[index]? = some memory := by
    simpa only [swapEntryStore, chargedStore] using hmemory
  have cfinal := calledSwapStore_credits s op index rest address value memory hc
  have hleave := wp_leave_wasm cfg fuel rest (calledSwapStore s op index address value memory)
    limits base [.i32 (readI32 memory address.toNat)] (swapFrame callee memory address) saved callers post
    rfl rfl rfl cfinal
  have hleave' : WP cfg (fuel + 1) (.next (atCode (calledSwapStore s op index address value memory) limits
      (base.toArray.push (.i32 (readI32 memory address.toNat))) (swapFrame callee memory address)
      (saved :: callers) [])) rest post := by
    have ht : WP cfg fuel (.next (atCode (calledSwapStore s op index address value memory) limits
        (base ++ [Value.i32 (readI32 memory address.toNat)]).toArray saved callers saved.code)) rest post := by
      simpa only [saved, atCode] using hnext
    simpa using hleave ht
  have hbody := wp_swap cfg (fuel + 1) rest (swapEntryStore s op) limits base.toArray callee
    (saved :: callers) [] address value calleeModule index memory post rfl rfl (by simp [callee])
    hm hindex hmem hbound ha.2.2.2
  have hbody' := hbody hleave'
  rw [show fuel + 1 + 7 = fuel + 8 by omega] at hbody'
  have hact : activationGas op
      (wasmLocals WNear.Binary.ValueReturnBorrow.swapFunction [.i32 address, .i32 value]) = 10 * op := by
    simp [wasmLocals, WNear.Binary.ValueReturnBorrow.swapFunction, activationGas, ValType.default]
  have hentry := wp_call_wasm cfg (fuel + 8) (7 * op + rest) s limits base [.i32 address, .i32 value]
    frame callers code 672 functionAddress callerModule WNear.Binary.ValueReturnBorrow.nonnullSignature inst
    WNear.Binary.ValueReturnBorrow.swapFunction post hmodule hfunctionIndex hfunction rfl hdepth
  rw [hact] at hentry
  have hc' : s.host.gas.Credits (cfg.regularOpCost + (10 * op + (7 * op + rest))) := hc.mono (by dsimp [op]; omega)
  have hentry' := hentry hc'
  have hbody'' : WP cfg (fuel + 8) (.next (wasmCallee (swapEntryStore s op) limits base frame callers code
      WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction
      [.i32 address, .i32 value])) (7 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.ValueReturnBorrow.nonnullSignature,
      WNear.Binary.ValueReturnBorrow.swapFunction, callee, saved, atCode, ValType.default, op] using hbody'
  have hall := hentry' hbody''
  rw [show fuel + 8 + 1 = fuel + 9 by omega,
    show cfg.regularOpCost + (10 * op + (7 * op + rest)) = 18 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  exact hall

def releaseFrame (frame : CallFrame) (counter : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 0 (.i32 counter)}

/-- The release prefix follows the actual stored counter pointer, then reads
and decrements that counter modulo 2^32. Both reads precede the nested write. -/
theorem wp_release_prepare (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (record counter : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hrecord : frame.locals[0]? = some (.i32 record)) (hsize : 1 ≤ frame.locals.size)
    (hcounter : readI32 memory record.toNat = counter)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hrb : record.toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      ((stack.push (.i32 counter)).push (.i32 (readI32 memory counter.toNat + 4294967295)))
      (releaseFrame frame counter) callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      ([.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_tee 0,
        .local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 4294967295,
        .i32_binop .add] ++ code))) (7 * cfg.regularOpCost + rest) post := by
  let frame' := releaseFrame frame counter
  have hcptr : frame'.locals[0]? = some (.i32 counter) := by
    simp [frame', releaseFrame, show 0 < frame.locals.size by omega]
  have hm1 : (paid s cfg.regularOpCost 1).modules[frame.inst]? = some mi := by
    simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by
    simpa only [paid, chargedStore] using hmem
  have hm4 : (paid s cfg.regularOpCost 4).modules[frame'.inst]? = some mi := by
    simpa only [paid, chargedStore, frame', releaseFrame] using hm
  have hmem4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by
    simpa only [paid, chargedStore] using hmem
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) _ s limits stack frame callers _ 0 (.i32 record) post hrecord (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 5) _ (paid s cfg.regularOpCost 1) limits stack frame callers _
    {align := 2, offset := 0} record mi index memory post hm1 hi hmem1 (by simpa using hrb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  simp only [Nat.add_zero, hcounter]
  apply wp_local_tee cfg (fuel + 4) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ 0 (.i32 counter) post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid s cfg.regularOpCost 3) limits _ frame' callers _ 0 (.i32 counter) post hcptr
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 4) limits _ frame' callers _
    {align := 2, offset := 0} counter mi index memory post hm4 hi hmem4 (by simpa using hcb)
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 5) limits _ frame' callers _ 4294967295 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  apply wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 6) limits _ frame' callers code
    (readI32 memory counter.toNat) 4294967295 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  · exact hnext

def releasedStore (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) : Store NearState :=
  chargedStore (calledSwapStore (paid s op 7) op index counter (readI32 memory counter.toNat + 4294967295) memory) op

/-- Actual f431 cleanup, including the real call to f672 and the discarded old
counter. Counter/record addresses can alias; only their actual read bounds
and structural function linkage are assumed. -/
theorem wp_release (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (record counter : UInt32) (mi calleeModule : ModuleInst)
    (functionAddress inst index : Nat) (memory : Memory) (post : Post)
    (hrecord : frame.locals[0]? = some (.i32 record)) (hsize : 1 ≤ frame.locals.size)
    (hcounter : readI32 memory record.toNat = counter)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hfindex : mi.funcAddrs[672]? = some functionAddress)
    (hf : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcm : s.modules[inst]? = some calleeModule) (hcmi : calleeModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hrb : record.toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (26 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (releasedStore s cfg.regularOpCost index counter memory)
      limits base.toArray (releaseFrame frame counter) callers code)) rest post) :
    WP cfg (fuel + 17) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnBorrow.releaseBody ++ code))) (26 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 7
  let frame' := releaseFrame frame counter
  let value := readI32 memory counter.toNat + 4294967295
  let swapped := calledSwapStore prepared op index counter value memory
  have cp : prepared.host.gas.Credits (19 * op + rest) := paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  have cs : swapped.host.gas.Credits (op + rest) :=
    calledSwapStore_credits prepared op index (op + rest) counter value memory (cp.mono (by omega))
  have hdrop := wp_drop cfg fuel rest swapped limits base.toArray frame' callers code
    (.i32 (readI32 memory counter.toNat)) post cs
  have hdrop' := hdrop hnext
  have hm7 : prepared.modules[frame'.inst]? = some mi := by
    simpa only [prepared, frame', releaseFrame, paid, chargedStore] using hm
  have hf7 : prepared.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction) := by
    simpa only [prepared, paid, chargedStore] using hf
  have hcm7 : prepared.modules[inst]? = some calleeModule := by
    simpa only [prepared, paid, chargedStore] using hcm
  have hmem7 : prepared.mems[index]? = some memory := by
    simpa only [prepared, paid, chargedStore] using hmem
  have hcall := wp_call_swap cfg (fuel + 1) (op + rest) prepared limits base frame' callers (.drop :: code)
    counter value mi calleeModule functionAddress inst index memory post hm7 hfindex hf7 hcm7 hcmi hmem7 hcb hdepth
    (cp.mono (by omega))
  have hdrop'' : WP cfg (fuel + 1) (.next (atCode swapped limits
      (base ++ [Value.i32 (readI32 memory counter.toNat)]).toArray frame' callers (.drop :: code))) (op + rest) post := by
    simpa using hdrop'
  have hcall' := hcall hdrop''
  rw [show fuel + 1 + 9 = fuel + 10 by omega,
    show 18 * cfg.regularOpCost + (op + rest) = 19 * op + rest by dsimp [op]; omega] at hcall'
  have hcall'' : WP cfg (fuel + 10) (.next (atCode prepared limits
      ((base.toArray.push (.i32 counter)).push (.i32 value)) frame' callers (.call 672 :: .drop :: code)))
      (19 * op + rest) post := by
    simpa using hcall'
  have hprepare := wp_release_prepare cfg (fuel + 10) (19 * op + rest) s limits base.toArray frame callers
    (.call 672 :: .drop :: code) record counter mi index memory post hrecord hsize hcounter hm hi hmem hrb hcb
    (hc.mono (by dsimp [op]; omega))
  have hprepare' := hprepare hcall''
  rw [show fuel + 10 + 7 = fuel + 17 by omega,
    show 7 * cfg.regularOpCost + (19 * op + rest) = 26 * cfg.regularOpCost + rest by dsimp [op]; omega] at hprepare'
  exact hprepare'

theorem calledSwapStore_gas (s : Store NearState) (op index rest : Nat) (address value : UInt32)
    (memory : Memory) (hc : s.host.gas.Credits (18 * op + rest)) :
    (calledSwapStore s op index address value memory).host.gas.burnt = s.host.gas.burnt + 18 * op ∧
    (calledSwapStore s op index address value memory).host.gas.promises = s.host.gas.promises := by
  have hop := GasCounter.burn_credits s.host.gas op (17 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (7 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hb := swapStore_gas (swapEntryStore s op) op index rest address value memory ha.2.2.2
  refine ⟨?_, hb.2.trans (ha.2.2.1.trans hop.2.2.1)⟩
  rw [show (calledSwapStore s op index address value memory).host.gas.burnt =
      (swapStore (swapEntryStore s op) op index address value memory).host.gas.burnt from rfl, hb.1]
  have he : (swapEntryStore s op).host.gas.burnt = s.host.gas.burnt + op + 10 * op := ha.2.1.trans (by rw [show (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op from hop.2.1])
  rw [he]; omega

theorem releasedStore_gas (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (26 * op + rest)) :
    (releasedStore s op index counter memory).host.gas.burnt = s.host.gas.burnt + 26 * op ∧
    (releasedStore s op index counter memory).host.gas.promises = s.host.gas.promises ∧
    (releasedStore s op index counter memory).host.gas.Credits rest := by
  let prepared := paid s op 7
  let value := readI32 memory counter.toNat + 4294967295
  let swapped := calledSwapStore prepared op index counter value memory
  have cp : prepared.host.gas.Credits (19 * op + rest) := paid_credits s op 7 _ (hc.mono (by omega))
  have hp := paid_gas s op 7 (19 * op + rest) (hc.mono (by omega))
  have hs := calledSwapStore_gas prepared op index (op + rest) counter value memory (cp.mono (by omega))
  have cs : swapped.host.gas.Credits (op + rest) := calledSwapStore_credits prepared op index (op + rest) counter value memory (cp.mono (by omega))
  have hd := GasCounter.burn_credits swapped.host.gas op rest cs
  refine ⟨?_, hd.2.2.1.trans (hs.2.trans hp.2), hd.2.2.2⟩
  change (chargedStore swapped op).host.gas.burnt = _
  rw [show (chargedStore swapped op).host.gas.burnt = swapped.host.gas.burnt + op from hd.2.1, hs.1, hp.1]
  omega

theorem releasedStore_resources (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    {releasedStore s op index counter memory with mems := s.mems, host := s.host} = s := by
  simp only [releasedStore, calledSwapStore, swapStore, swapEntryStore, paid, chargedStore, storeI32]

theorem releasedStore_memory (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (releasedStore s op index counter memory).mems[index]? =
      some (writeI32 memory counter.toNat (readI32 memory counter.toNat + 4294967295)) := by
  have hp : (swapEntryStore (paid s op 7) op).mems[index]? = some memory := by
    simpa only [swapEntryStore, chargedStore, paid] using hm
  have h := swapStore_memory (swapEntryStore (paid s op 7) op) op index counter
    (readI32 memory counter.toNat + 4294967295) memory hp
  simpa only [releasedStore, calledSwapStore, chargedStore] using h

/-- Complete active f431, including nested f672 and both free frame exits.
The 26 charged units plus its nine-unit entry explain the validated 35. -/
theorem wp_release_return (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (moduleInst : Nat) (record counter : UInt32)
    (mi calleeModule : ModuleInst) (functionAddress inst index : Nat) (memory : Memory)
    (hrecord : locals[0]? = some (.i32 record)) (hsize : 1 ≤ locals.size)
    (hcounter : readI32 memory record.toNat = counter)
    (hm : s.modules[moduleInst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hfindex : mi.funcAddrs[672]? = some functionAddress)
    (hf : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcm : s.modules[inst]? = some calleeModule) (hcmi : calleeModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hrb : record.toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (26 * cfg.regularOpCost + rest)) :
    WP cfg 18 (.next (atCode s limits #[] (WNear.Proofs.StorePair.voidFrame locals moduleInst) []
      WNear.Binary.ValueReturnBorrow.releaseBody)) (26 * cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (releasedStore s cfg.regularOpCost index counter memory) ∧ error = none) := by
  have c := (releasedStore_gas s cfg.regularOpCost index rest counter memory hc).2.2
  have hfinish := WNear.Proofs.StorePair.wp_finish_void cfg 0 rest (releasedStore s cfg.regularOpCost index counter memory)
    limits (locals.set! 0 (.i32 counter)) moduleInst
    (fun remaining final error => remaining = rest ∧
      final = .done [] (releasedStore s cfg.regularOpCost index counter memory) ∧ error = none) c ⟨rfl, rfl, rfl⟩
  have h := wp_release cfg 1 rest s limits [] (WNear.Proofs.StorePair.voidFrame locals moduleInst) [] []
    record counter mi calleeModule functionAddress inst index memory
    (fun remaining final error => remaining = rest ∧
      final = .done [] (releasedStore s cfg.regularOpCost index counter memory) ∧ error = none)
    hrecord hsize hcounter hm hi hfindex hf hcm hcmi hmem hrb hcb hdepth hc
  apply h
  exact hfinish

end WNear.Proofs.ValueReturnBorrowCounters
