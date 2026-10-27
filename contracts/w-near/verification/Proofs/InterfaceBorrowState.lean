import Binary.InterfaceBorrow
import Proofs.ValueReturnAcquire
import Proofs.ValueReturnOuter
import NearVM.MeteredLoopRules

namespace WNear.Proofs.InterfaceBorrow
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
open WNear.Proofs.ValueReturnBorrowCounters (calledSwapStore calledSwapStore_credits calledSwapStore_gas swapEntryStore swapStore swapStore_memory wp_call_swap)
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
def releaseFrame (frame : CallFrame) (counter : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 0 (.i32 counter)}

/-- The release prefix follows the actual stored counter pointer, then reads
and increments that counter modulo 2^32. Both reads precede the nested write. -/
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
      ((stack.push (.i32 counter)).push (.i32 (readI32 memory counter.toNat + 1)))
      (releaseFrame frame counter) callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      ([.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_tee 0,
        .local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 1,
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
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 5) limits _ frame' callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  apply wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 6) limits _ frame' callers code
    (readI32 memory counter.toNat) 1 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  · exact hnext

def releasedStore (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) : Store NearState :=
  chargedStore (calledSwapStore (paid s op 7) op index counter (readI32 memory counter.toNat + 1) memory) op

/-- Actual f442 cleanup, including the real call to f672 and the discarded old
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
      (WNear.Binary.InterfaceBorrow.releaseBody ++ code))) (26 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 7
  let frame' := releaseFrame frame counter
  let value := readI32 memory counter.toNat + 1
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

theorem releasedStore_gas (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (26 * op + rest)) :
    (releasedStore s op index counter memory).host.gas.burnt = s.host.gas.burnt + 26 * op ∧
    (releasedStore s op index counter memory).host.gas.promises = s.host.gas.promises ∧
    (releasedStore s op index counter memory).host.gas.Credits rest := by
  let prepared := paid s op 7
  let value := readI32 memory counter.toNat + 1
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
      some (writeI32 memory counter.toNat (readI32 memory counter.toNat + 1)) := by
  have hp : (swapEntryStore (paid s op 7) op).mems[index]? = some memory := by
    simpa only [swapEntryStore, chargedStore, paid] using hm
  have h := swapStore_memory (swapEntryStore (paid s op 7) op) op index counter
    (readI32 memory counter.toNat + 1) memory hp
  simpa only [releasedStore, calledSwapStore, chargedStore] using h

/-- Complete active f442, including nested f672 and both free frame exits.
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
      WNear.Binary.InterfaceBorrow.releaseBody)) (26 * cfg.regularOpCost + rest)
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



def releaseEntryStore (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def calledReleaseStore (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :=
  releasedStore (releaseEntryStore s op) op index counter memory

theorem calledReleaseStore_credits (s : Store NearState) (op index rest : Nat) (counter : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (36 * op + rest)) : (calledReleaseStore s op index counter memory).host.gas.Credits rest := by
  apply (releasedStore_gas (releaseEntryStore s op) op index rest counter memory _).2.2
  apply WNear.Proofs.StorePair.charged_credits
  apply WNear.Proofs.StorePair.charged_credits
  exact hc.mono (by omega)

/-- Actual f442 call: follows its stored counter pointer, executes f672's swap,
and returns after discarding the previous counter. -/
theorem wp_call_release (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (record counter : UInt32) (address inst swapAddress swapInst index : Nat)
    (callerModule releaseModule swapModule : ModuleInst) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some callerModule) (ha : callerModule.funcAddrs[442]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.InterfaceBorrow.releaseFunction))
    (hcm : s.modules[inst]? = some releaseModule) (hi : releaseModule.memAddrs[0]? = some index)
    (hsa : releaseModule.funcAddrs[672]? = some swapAddress)
    (hsf : s.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature swapInst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hsm : s.modules[swapInst]? = some swapModule) (hsi : swapModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hcounter : readI32 memory record.toNat = counter)
    (hrb : record.toNat + 4 ≤ memory.byteSize) (hcb : counter.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (36 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledReleaseStore s cfg.regularOpCost index counter memory) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 19) (.next (atCode s limits (base ++ [Value.i32 record]).toArray
      frame callers (.call 442 :: code))) (36 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := releaseEntryStore s op
  let leaf : CallFrame := {locals := #[.i32 record], inst, arity := 0, height := base.length, labels := [], code := []}
  let finished := releaseFrame leaf counter
  let saved := {frame with code}
  have h0 : s.host.gas.Credits (op + (9 * op + (26 * op + rest))) := hc.mono (by dsimp [op]; omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 : active.host.gas.Credits (26 * op + rest) := WNear.Proofs.StorePair.charged_credits (chargedStore s op) _ _ h1
  have hfinal := calledReleaseStore_credits s op index rest counter memory hc
  have leaveRule := wp_leave_wasm cfg fuel rest (calledReleaseStore s op index counter memory) limits base [] finished saved callers post rfl rfl rfl hfinal
  simp only [List.append_nil] at leaveRule
  have hleave : WP cfg (fuel + 1) (.next (atCode (calledReleaseStore s op index counter memory) limits base.toArray finished (saved :: callers) [])) rest post := by
    apply leaveRule
    simpa only [saved, atCode] using hnext
  have hm' : active.modules[inst]? = some releaseModule := by simpa only [active, releaseEntryStore, chargedStore] using hcm
  have hf' : active.funcs[swapAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature swapInst WNear.Binary.ValueReturnBorrow.swapFunction) := by
    simpa only [active, releaseEntryStore, chargedStore] using hsf
  have hsm' : active.modules[swapInst]? = some swapModule := by simpa only [active, releaseEntryStore, chargedStore] using hsm
  have hmem' : active.mems[index]? = some memory := by simpa only [active, releaseEntryStore, chargedStore] using hmem
  have nestedDepth : (saved :: callers).length + 1 < limits.maxCallDepth := by simp only [List.length_cons]; omega
  have bodyRule := wp_release cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] record counter
    releaseModule swapModule swapAddress swapInst index memory post
  have bodyShape := bodyRule rfl (by simp [leaf])
  have bodyEnv := bodyShape hcounter hm' hi hsa hf' hsm' hsi hmem' hrb hcb nestedDepth
  have bodyPaid := bodyEnv h2
  have hbody := bodyPaid hleave
  have activation : activationGas op (wasmLocals WNear.Binary.InterfaceBorrow.releaseFunction [.i32 record]) = 9 * op := by
    simp [wasmLocals, WNear.Binary.InterfaceBorrow.releaseFunction, activationGas]
  have depth : callers.length + 1 < limits.maxCallDepth := by omega
  have callRule := wp_call_wasm cfg ((fuel + 1) + 17) (26 * op + rest) s limits base [.i32 record]
    frame callers code 442 address callerModule WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.InterfaceBorrow.releaseFunction post hm ha hf rfl depth
  rw [activation] at callRule
  have callPaid := callRule h0
  have bodyNext : WP cfg ((fuel + 1) + 17) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.InterfaceBorrow.releaseFunction [.i32 record])) (26 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.InterfaceBorrow.releaseFunction,
      WNear.Binary.ValueReturnBorrow.voidSignature, leaf, saved, atCode, List.map_nil,
      List.append_nil, List.length_nil, Array.append_empty] using hbody
  have result := callPaid bodyNext
  have budget : cfg.regularOpCost + (9 * op + (26 * op + rest)) = 36 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [budget] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result


def takeFrame (frame : CallFrame) (cell : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 1 (.i32 cell)}
def takeStore (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :=
  paid (calledSwapStore (paid s op 7) op index cell 4294967295 memory) op 4

def takeEntryStore (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def calledTakeStore (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :=
  takeStore (takeEntryStore s op) op index cell memory

def guardStore (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :=
  paid (calledTakeStore (paid s op 1) op index cell memory) op 2
def reserved (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid s op 5) globalIndex (.i32 (sp - 16))
def recordMemory (memory : Memory) (out cell : UInt32) : Memory :=
  writeI32 (writeI32 memory (out.toNat + 4) cell) out.toNat (cell + 4)
def recordStore (s : Store NearState) (op index : Nat) (out cell : UInt32) (memory : Memory) : Store NearState :=
  storeI32 (paid (storeI32 (paid s op 3) index (out.toNat + 4) memory cell) op 5) index out.toNat
    (writeI32 memory (out.toNat + 4) cell) (cell + 4)
def acquiredFrame (frame : CallFrame) (cell : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 4 (.i32 cell)}
def acquireFrame (frame : CallFrame) (sp cell : UInt32) : CallFrame :=
  acquiredFrame {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))} cell

def acquireStore (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) : Store NearState :=
  setGlobal (paid (recordStore (guardStore (reserved s op globalIndex sp) op memoryIndex cell memory)
    op memoryIndex out cell (writeI32 memory cell.toNat 4294967295)) op 4) globalIndex (.i32 sp)
def acquireEntryStore (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11 * op)
def calledAcquireStore (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) := acquireStore (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory


end WNear.Proofs.InterfaceBorrow
