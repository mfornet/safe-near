import Binary.ValueReturnAcquire
import Proofs.ValueReturnBorrowCounters

/-! Accepted acquisition through the deployed RefCell instructions. -/
namespace WNear.Proofs.ValueReturnAcquire
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
open WNear.Proofs.ValueReturnBorrowCounters
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def nextCount (memory : Memory) (cell : UInt32) : UInt32 := readI32 memory cell.toNat + 1
def incrementFrame (frame : CallFrame) (memory : Memory) (cell : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 1 (.i32 (nextCount memory cell))}

/-- Actual signed guard. Rejected counts take the separate zero-return path;
this contract covers precisely the nonzero accepted branch. -/
theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (haccept : Numeric.irelop32 .ge_s (nextCount memory cell) 1 = true)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits stack
      (incrementFrame frame memory cell) callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.ValueReturnAcquire.guard ++ WNear.Binary.ValueReturnAcquire.rejected)))
      (8 * cfg.regularOpCost + rest) post := by
  let block := emptyBlockFrame frame stack.size code
  let frame' := incrementFrame frame memory cell
  have hm1 : (paid s cfg.regularOpCost 1).modules[block.inst]? = some mi := by
    simpa only [paid, chargedStore, block, emptyBlockFrame] using hm
  have hmem1 : (paid s cfg.regularOpCost 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hcond : Numeric.bool (Numeric.irelop32 .ge_s (nextCount memory cell) 1) ≠ 0 := by simp [haccept, Numeric.bool]
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 7) _ s limits stack block callers _ 0 (.i32 cell) post hcell (hc.mono (by omega))
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 6) _ (paid s cfg.regularOpCost 1) limits stack block callers _
    {align := 2, offset := 0} cell mi index memory post hm1 hi hmem1 (by simpa using hb)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 5) _ (paid s cfg.regularOpCost 2) limits _ block callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 4) _ (paid s cfg.regularOpCost 3) limits stack block callers _ (readI32 memory cell.toNat) 1 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 3) _ (paid s cfg.regularOpCost 4) limits stack block callers _ 1 (.i32 (nextCount memory cell)) post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ (paid s cfg.regularOpCost 5) limits _ (emptyBlockFrame frame' stack.size code) callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_relop cfg (fuel + 1) _ (paid s cfg.regularOpCost 6) limits stack
    (emptyBlockFrame frame' stack.size code) callers _ .ge_s (nextCount memory cell) 1 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 7) limits stack frame' callers code
    WNear.Binary.ValueReturnAcquire.rejected _ post hcond
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  · exact hnext

def incrementStore (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) : Store NearState :=
  paid (calledSwapStore (paid s op 10) op index cell (nextCount memory cell) memory) op 2

/-- f494's tail invokes the actual swap helper and then returns its cell pointer. -/
theorem wp_incrementTail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell count : UInt32) (mi calleeModule : ModuleInst)
    (functionAddress inst index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell)) (hcount : frame.locals[1]? = some (.i32 count))
    (hm : s.modules[frame.inst]? = some mi) (hfindex : mi.funcAddrs[672]? = some functionAddress)
    (hf : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcm : s.modules[inst]? = some calleeModule) (hcmi : calleeModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (22 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (paid (calledSwapStore (paid s cfg.regularOpCost 2) cfg.regularOpCost index cell count memory) cfg.regularOpCost 2)
      limits (base.toArray.push (.i32 cell)) frame callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnAcquire.incrementTail ++ code))) (22 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 2
  let swapped := calledSwapStore prepared op index cell count memory
  have cp : prepared.host.gas.Credits (20 * op + rest) := paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  have cs : swapped.host.gas.Credits (2 * op + rest) := calledSwapStore_credits prepared op index _ cell count memory (cp.mono (by omega))
  have hget := wp_local_get cfg fuel rest (paid swapped op 1) limits base.toArray frame callers code 0 (.i32 cell) post hcell
    (paid_credits swapped op 1 _ (cs.mono (by omega))) hnext
  have hdrop := wp_drop cfg (fuel + 1) (op + rest) swapped limits base.toArray frame callers (.local_get 0 :: code)
    (.i32 (readI32 memory cell.toNat)) post (cs.mono (by omega))
  have hdrop' := hdrop hget
  rw [show fuel + 1 + 1 = fuel + 2 by omega,
    show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at hdrop'
  have hm2 : prepared.modules[frame.inst]? = some mi := by simpa only [prepared, paid, chargedStore] using hm
  have hf2 : prepared.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction) := by
    simpa only [prepared, paid, chargedStore] using hf
  have hcm2 : prepared.modules[inst]? = some calleeModule := by simpa only [prepared, paid, chargedStore] using hcm
  have hmem2 : prepared.mems[index]? = some memory := by simpa only [prepared, paid, chargedStore] using hmem
  have hcall := wp_call_swap cfg (fuel + 2) (2 * op + rest) prepared limits base frame callers
    (.drop :: .local_get 0 :: code) cell count mi calleeModule functionAddress inst index memory post
    hm2 hfindex hf2 hcm2 hcmi hmem2 hb hdepth (cp.mono (by omega))
  have ht : WP cfg (fuel + 2) (.next (atCode swapped limits
      (base ++ [Value.i32 (readI32 memory cell.toNat)]).toArray frame callers (.drop :: .local_get 0 :: code)))
      (2 * op + rest) post := by
    simpa using hdrop'
  have hcall' := hcall ht
  rw [show fuel + 2 + 9 = fuel + 11 by omega,
    show 18 * cfg.regularOpCost + (2 * op + rest) = 20 * op + rest by dsimp [op]; omega] at hcall'
  have hcall'' : WP cfg (fuel + 11) (.next (atCode prepared limits
      ((base.toArray.push (.i32 cell)).push (.i32 count)) frame callers (.call 672 :: .drop :: .local_get 0 :: code)))
      (20 * op + rest) post := by simpa using hcall'
  rw [show 22 * cfg.regularOpCost + rest = cfg.regularOpCost + (21 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 12) _ s limits base.toArray frame callers _ 0 (.i32 cell) post hcell (hc.mono (by omega))
  rw [show 21 * cfg.regularOpCost + rest = cfg.regularOpCost + (20 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 11) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 1 (.i32 count) post hcount
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  · exact hcall''

/-- Primitive same-module links for the actual two deployed counter helpers. -/
structure Links (s : Store NearState) (mi : ModuleInst) (inst : Nat) : Prop where
  module : s.modules[inst]? = some mi
  swap : ∃ address, mi.funcAddrs[672]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  increment : ∃ address, mi.funcAddrs[494]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.ValueReturnAcquire.incrementSignature inst WNear.Binary.ValueReturnAcquire.incrementFunction)

theorem links_resources (s t : Store NearState) (mi : ModuleInst) (inst : Nat)
    (hmodule : t.modules = s.modules) (hfuncs : t.funcs = s.funcs) (h : Links s mi inst) : Links t mi inst := by
  rcases h with ⟨hm, ⟨a, ha, hf⟩, ⟨b, hb, hg⟩⟩
  exact ⟨by simpa only [hmodule] using hm, ⟨a, ha, by simpa only [hfuncs] using hf⟩,
    ⟨b, hb, by simpa only [hfuncs] using hg⟩⟩

theorem links_paid (s : Store NearState) (mi : ModuleInst) (inst op n : Nat) (h : Links s mi inst) :
    Links (paid s op n) mi inst := by
  have hr := WNear.Proofs.StorePairCaller.paid_resources s op n
  exact links_resources s _ mi inst (congrArg (fun x => x.modules) hr) (congrArg (fun x => x.funcs) hr) h

theorem links_charge (s : Store NearState) (mi : ModuleInst) (inst cost : Nat) (h : Links s mi inst) :
    Links (chargedStore s cost) mi inst := links_resources s _ mi inst rfl rfl h

theorem links_setGlobal (s : Store NearState) (mi : ModuleInst) (inst index : Nat) (value : Value)
    (h : Links s mi inst) : Links (setGlobal s index value) mi inst := links_resources s _ mi inst rfl rfl h

/-- The complete accepted f494 body: eight checked opcodes, a real nested swap,
and the nonzero cell result, retaining the outer continuation. -/
theorem wp_increment (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell)) (hsize : 2 ≤ frame.locals.size)
    (hlinks : Links s mi frame.inst) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (haccept : Numeric.irelop32 .ge_s (nextCount memory cell) 1 = true)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (30 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (incrementStore s cfg.regularOpCost index cell memory) limits
      (base.toArray.push (.i32 cell)) (incrementFrame frame memory cell) callers code)) rest post) :
    WP cfg (fuel + 22) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnAcquire.incrementBody ++ code))) (30 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let checked := paid s op 8
  let frame' := incrementFrame frame memory cell
  have ha : frame'.locals[0]? = some (.i32 cell) := by simpa [frame', incrementFrame] using hcell
  have hv : frame'.locals[1]? = some (.i32 (nextCount memory cell)) := by
    simp [frame', incrementFrame, show 1 < frame.locals.size by omega]
  have hl := links_paid s mi frame.inst op 8 hlinks
  rcases hl.swap with ⟨address, had, hfn⟩
  have hm : checked.modules[frame'.inst]? = some mi := by simpa only [checked, frame', incrementFrame] using hl.module
  have hmem8 : checked.mems[index]? = some memory := by simpa only [checked, paid, chargedStore] using hmem
  have cp : checked.host.gas.Credits (22 * op + rest) := paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))
  have ht := wp_incrementTail cfg fuel rest checked limits base frame' callers code cell (nextCount memory cell)
    mi mi address frame.inst index memory post ha hv hm had hfn hl.module hi hmem8 hb hdepth cp
  have ht' : WP cfg (fuel + 13) (.next (atCode checked limits base.toArray frame' callers
      (WNear.Binary.ValueReturnAcquire.incrementTail ++ code))) (22 * op + rest) post := by
    apply ht
    simpa only [incrementStore, checked, frame', op, WNear.Proofs.ValueReturnBorrow.paid_add] using hnext
  have hg := wp_guard cfg (fuel + 13) (22 * op + rest) s limits base.toArray frame callers
    (WNear.Binary.ValueReturnAcquire.incrementTail ++ code) cell mi index memory post hcell hlinks.module hi hmem hb haccept
    (hc.mono (by dsimp [op]; omega))
  have hg' := hg ht'
  rw [show fuel + 13 + 8 = fuel + 21 by omega,
    show 8 * cfg.regularOpCost + (22 * op + rest) = 30 * op + rest by dsimp [op]; omega] at hg'
  have hb' := wp_block_empty cfg (fuel + 21) (30 * op + rest) s limits base.toArray frame callers
    (WNear.Binary.ValueReturnAcquire.guard ++ WNear.Binary.ValueReturnAcquire.rejected)
    (WNear.Binary.ValueReturnAcquire.incrementTail ++ code) post hc
  have hall := hb' hg'
  rw [show fuel + 21 + 1 = fuel + 22 by omega] at hall
  simpa only [WNear.Binary.ValueReturnAcquire.incrementBody, List.cons_append, List.nil_append] using hall

theorem incrementStore_gas (s : Store NearState) (op index rest : Nat) (cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (30 * op + rest)) :
    (incrementStore s op index cell memory).host.gas.burnt = s.host.gas.burnt + 30 * op ∧
    (incrementStore s op index cell memory).host.gas.promises = s.host.gas.promises ∧
    (incrementStore s op index cell memory).host.gas.Credits rest := by
  let prepared := paid s op 10
  let swapped := calledSwapStore prepared op index cell (nextCount memory cell) memory
  have cp : prepared.host.gas.Credits (20 * op + rest) := paid_credits s op 10 _ (hc.mono (by omega))
  have hp := paid_gas s op 10 (20 * op + rest) (hc.mono (by omega))
  have hs := calledSwapStore_gas prepared op index (2 * op + rest) cell (nextCount memory cell) memory (cp.mono (by omega))
  have cs : swapped.host.gas.Credits (2 * op + rest) := calledSwapStore_credits prepared op index _ cell (nextCount memory cell) memory (cp.mono (by omega))
  have hd := paid_gas swapped op 2 rest cs
  refine ⟨?_, hd.2.trans (hs.2.trans hp.2), paid_credits swapped op 2 rest cs⟩
  change (paid swapped op 2).host.gas.burnt = _
  rw [hd.1, hs.1, hp.1]; omega

def incrementEntryStore (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (9 * op)
def calledIncrementStore (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) : Store NearState :=
  incrementStore (incrementEntryStore s op) op index cell memory

/-- Actual direct f494 call; primitive links fix the callee, with no assumed
execution result. The activation, nested swap and final return are included. -/
theorem wp_call_increment (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlinks : Links s mi frame.inst) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (haccept : Numeric.irelop32 .ge_s (nextCount memory cell) 1 = true)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (40 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledIncrementStore s cfg.regularOpCost index cell memory) limits
      (base ++ [Value.i32 cell]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 24) (.next (atCode s limits (base ++ [Value.i32 cell]).toArray frame callers
      (.call 494 :: code))) (40 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee : CallFrame :=
    {locals := #[.i32 cell, .i32 0]
     inst := frame.inst
     arity := 1
     height := base.length
     labels := []
     code := []}
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (39 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (9 * op) (30 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hl := links_charge _ mi frame.inst (9 * op) (links_charge s mi frame.inst op hlinks)
  have hmem' : (incrementEntryStore s op).mems[index]? = some memory := hmem
  have c := (incrementStore_gas (incrementEntryStore s op) op index rest cell memory (ha.2.2.2.mono (by omega))).2.2
  have hleave := wp_leave_wasm cfg fuel rest (calledIncrementStore s op index cell memory) limits base [.i32 cell]
    (incrementFrame callee memory cell) saved callers post rfl rfl rfl c
  have ht : WP cfg fuel (.next (atCode (calledIncrementStore s op index cell memory) limits
      (base ++ [Value.i32 cell]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have hleave' := hleave ht
  have hleave'' : WP cfg (fuel + 1) (.next (atCode (calledIncrementStore s op index cell memory) limits
      (base.toArray.push (.i32 cell)) (incrementFrame callee memory cell) (saved :: callers) [])) rest post := by
    simpa using hleave'
  have hbody := wp_increment cfg (fuel + 1) rest (incrementEntryStore s op) limits base callee (saved :: callers) [] cell
    mi index memory post rfl (by simp [callee]) hl hi hmem' hb haccept (by simpa using hdepth) ha.2.2.2
  have hbody' := hbody hleave''
  rw [show fuel + 1 + 22 = fuel + 23 by omega] at hbody'
  rcases hlinks.increment with ⟨address, had, hfn⟩
  have he := wp_call_wasm cfg (fuel + 23) (30 * op + rest) s limits base [.i32 cell] frame callers code 494 address
    mi WNear.Binary.ValueReturnAcquire.incrementSignature frame.inst WNear.Binary.ValueReturnAcquire.incrementFunction
    post hlinks.module had hfn rfl (by omega)
  have hact : activationGas op (wasmLocals WNear.Binary.ValueReturnAcquire.incrementFunction [.i32 cell]) = 9 * op := by
    simp [wasmLocals, WNear.Binary.ValueReturnAcquire.incrementFunction, activationGas, ValType.default]
  rw [hact] at he
  have he' := he (hc.mono (by dsimp [op]; omega))
  have hbody'' : WP cfg (fuel + 23) (.next (wasmCallee (incrementEntryStore s op) limits base frame callers code
      WNear.Binary.ValueReturnAcquire.incrementSignature frame.inst WNear.Binary.ValueReturnAcquire.incrementFunction [.i32 cell]))
      (30 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.ValueReturnAcquire.incrementSignature,
      WNear.Binary.ValueReturnAcquire.incrementFunction, callee, saved, atCode, ValType.default, op] using hbody'
  have hall := he' hbody''
  rw [show fuel + 23 + 1 = fuel + 24 by omega,
    show cfg.regularOpCost + (9 * op + (30 * op + rest)) = 40 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  exact hall

def guardStore (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) : Store NearState :=
  paid (calledIncrementStore (paid s op 1) op index cell memory) op 2

def acquiredFrame (frame : CallFrame) (cell : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 4 (.i32 cell)}

/-- The actual f429 block invokes f494 and branches over panic precisely when
its accepted result is nonzero. Its complete nested call is proved above. -/
theorem wp_acquireGuard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[1]? = some (.i32 cell)) (_hsize : 5 ≤ frame.locals.size)
    (hlinks : Links s mi frame.inst) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (haccept : Numeric.irelop32 .ge_s (nextCount memory cell) 1 = true) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (43 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (guardStore s cfg.regularOpCost index cell memory) limits
      base.toArray (acquiredFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 27) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.length code) callers
      (WNear.Binary.ValueReturnAcquire.acquireGuard ++ WNear.Binary.ValueReturnAcquire.acquirePanic)))
      (43 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let block := emptyBlockFrame frame base.length code
  let frame' := acquiredFrame frame cell
  let borrowed := calledIncrementStore (paid s op 1) op index cell memory
  have cp : (paid s op 1).host.gas.Credits (42 * op + rest) := paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  have hop := GasCounter.burn_credits (paid s op 1).host.gas op (41 * op + rest) (cp.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore (paid s op 1) op).host.gas (9 * op) (32 * op + rest)
    (hop.2.2.2.mono (by omega))
  have cb : borrowed.host.gas.Credits (2 * op + rest) :=
    (incrementStore_gas (incrementEntryStore (paid s op 1) op) op index (2 * op + rest) cell memory (ha.2.2.2.mono (by omega))).2.2
  have hbr := wp_br_if_block_nonzero cfg fuel rest (paid borrowed op 1) limits base.toArray frame' callers code
    WNear.Binary.ValueReturnAcquire.acquirePanic cell post hnonzero
    (paid_credits borrowed op 1 _ (cb.mono (by omega))) hnext
  have htee := wp_local_tee cfg (fuel + 1) (op + rest) borrowed limits base.toArray block callers
    (.br_if 0 :: WNear.Binary.ValueReturnAcquire.acquirePanic) 4 (.i32 cell) post (cb.mono (by omega))
  have hbr' : WP cfg (fuel + 1) (.next (atCode (paid borrowed op 1) limits (base.toArray.push (.i32 cell))
      {block with locals := block.locals.set! 4 (.i32 cell)} callers (.br_if 0 :: WNear.Binary.ValueReturnAcquire.acquirePanic)))
      (op + rest) post := by
    simpa [block, frame', acquiredFrame, emptyBlockFrame, op] using hbr
  simp only [paid] at hbr'
  have htee' := htee hbr'
  rw [show fuel + 1 + 1 = fuel + 2 by omega,
    show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at htee'
  have hl : Links (paid s op 1) mi block.inst := links_paid s mi frame.inst op 1 hlinks
  have hm1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hcall := wp_call_increment cfg (fuel + 2) (2 * op + rest) (paid s op 1) limits base block callers
    (.local_tee 4 :: .br_if 0 :: WNear.Binary.ValueReturnAcquire.acquirePanic) cell mi index memory post
    hl hi hm1 hb haccept hdepth (cp.mono (by omega))
  have htee'' : WP cfg (fuel + 2) (.next (atCode borrowed limits (base ++ [Value.i32 cell]).toArray block callers
      (.local_tee 4 :: .br_if 0 :: WNear.Binary.ValueReturnAcquire.acquirePanic))) (2 * op + rest) post := by
    simpa using htee'
  have hcall' := hcall htee''
  rw [show fuel + 2 + 24 = fuel + 26 by omega,
    show 40 * cfg.regularOpCost + (2 * op + rest) = 42 * op + rest by dsimp [op]; omega] at hcall'
  have hget := wp_local_get cfg (fuel + 26) (42 * op + rest) s limits base.toArray block callers
    (.call 494 :: .local_tee 4 :: .br_if 0 :: WNear.Binary.ValueReturnAcquire.acquirePanic) 1 (.i32 cell) post hcell
    (hc.mono (by dsimp [op]; omega))
  have hcall'' : WP cfg (fuel + 26) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 cell)) block callers
      (.call 494 :: .local_tee 4 :: .br_if 0 :: WNear.Binary.ValueReturnAcquire.acquirePanic))) (42 * op + rest) post := by
    simpa using hcall'
  have hall := hget hcall''
  rw [show fuel + 26 + 1 = fuel + 27 by omega,
    show cfg.regularOpCost + (42 * op + rest) = 43 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  simpa only [WNear.Binary.ValueReturnAcquire.acquireGuard, List.cons_append, List.nil_append] using hall

def recordMemory (memory : Memory) (out cell : UInt32) : Memory :=
  writeI32 (writeI32 memory (out.toNat + 4) cell) out.toNat (cell + 4)
def recordStore (s : Store NearState) (op index : Nat) (out cell : UInt32) (memory : Memory) : Store NearState :=
  storeI32 (paid (storeI32 (paid s op 3) index (out.toNat + 4) memory cell) op 5) index out.toNat
    (writeI32 memory (out.toNat + 4) cell) (cell + 4)

/-- Actual sequential record writes. They use the already incremented memory;
no non-aliasing premise is imposed on the cell and output record. -/
theorem wp_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hcell : frame.locals[1]? = some (.i32 cell))
    (hborrow : frame.locals[4]? = some (.i32 cell))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hwf : memory.wf) (hb : out.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (recordStore s cfg.regularOpCost index out cell memory) limits
      stack frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers
      ([.local_get 0, .local_get 4, .store .i32 none {align := 2, offset := 4},
        .local_get 0, .local_get 1, .i32_const 4, .i32_binop .add,
        .store .i32 none {align := 2, offset := 0}] ++ code))) (8 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let first := storeI32 (paid s op 3) index (out.toNat + 4) memory cell
  let memory' := writeI32 memory (out.toNat + 4) cell
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem2 : (paid s op 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hm4 : (paid first op 4).modules[frame.inst]? = some mi := by
    simpa only [first, storeI32, paid, chargedStore] using hm
  have hmem' : first.mems[index]? = some memory' := by
    apply storeI32_memory
    simpa only [paid, chargedStore] using hmem
  have hmem4 : (paid first op 4).mems[index]? = some memory' := by simpa only [paid, chargedStore] using hmem'
  have hs := writeI32_spec memory (out.toNat + 4) cell hwf (by omega)
  have cfirst : first.host.gas.Credits (5 * op + rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 7) _ s limits stack frame callers _ 0 (.i32 out) post hout (hc.mono (by omega))
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) _ (paid s op 1) limits _ frame callers _ 4 (.i32 cell) post hborrow
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_store cfg (fuel + 5) _ (paid s op 2) limits stack frame callers _ {align := 2, offset := 4}
    out cell mi index memory post hm2 hi hmem2 (by change out.toNat + 4 + 4 ≤ memory.byteSize; omega)
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) _ first limits stack frame callers _ 0 (.i32 out) post hout (cfirst.mono (by dsimp [op]; omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ (paid first op 1) limits _ frame callers _ 1 (.i32 cell) post hcell
  · exact paid_credits first op 1 _ (cfirst.mono (by dsimp [op]; omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ (paid first op 2) limits _ frame callers _ 4 post
  · exact paid_credits first op 2 _ (cfirst.mono (by dsimp [op]; omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) _ (paid first op 3) limits _ frame callers _ cell 4 post
  · exact paid_credits first op 3 _ (cfirst.mono (by dsimp [op]; omega))
  apply wp_i32_store cfg fuel rest (paid first op 4) limits stack frame callers code {align := 2, offset := 0}
    out (cell + 4) mi index memory' post hm4 hi hmem4 (by change out.toNat + 0 + 4 ≤ memory'.byteSize; dsimp [memory']; rw [hs.2.1]; omega)
  · exact paid_credits first op 4 _ (cfirst.mono (by dsimp [op]; omega))
  · exact hnext

theorem calledIncrementStore_gas (s : Store NearState) (op index rest : Nat) (cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (40 * op + rest)) :
    (calledIncrementStore s op index cell memory).host.gas.burnt = s.host.gas.burnt + 40 * op ∧
    (calledIncrementStore s op index cell memory).host.gas.promises = s.host.gas.promises ∧
    (calledIncrementStore s op index cell memory).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (39 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (9 * op) (30 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hb := incrementStore_gas (incrementEntryStore s op) op index rest cell memory ha.2.2.2
  refine ⟨?_, hb.2.1.trans (ha.2.2.1.trans hop.2.2.1), hb.2.2⟩
  change (incrementStore (incrementEntryStore s op) op index cell memory).host.gas.burnt = _
  rw [hb.1]
  have he : (incrementEntryStore s op).host.gas.burnt = s.host.gas.burnt + op + 9 * op :=
    ha.2.1.trans (by rw [show (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op from hop.2.1])
  rw [he]; omega

theorem guardStore_gas (s : Store NearState) (op index rest : Nat) (cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (43 * op + rest)) :
    (guardStore s op index cell memory).host.gas.burnt = s.host.gas.burnt + 43 * op ∧
    (guardStore s op index cell memory).host.gas.promises = s.host.gas.promises ∧
    (guardStore s op index cell memory).host.gas.Credits rest := by
  have cp := paid_credits s op 1 (42 * op + rest) (hc.mono (by omega))
  have hp := paid_gas s op 1 (42 * op + rest) (hc.mono (by omega))
  have hb := calledIncrementStore_gas (paid s op 1) op index (2 * op + rest) cell memory (cp.mono (by omega))
  have hd := paid_gas (calledIncrementStore (paid s op 1) op index cell memory) op 2 rest hb.2.2
  refine ⟨?_, hd.2.trans (hb.2.1.trans hp.2), paid_credits _ op 2 rest hb.2.2⟩
  change (paid (calledIncrementStore (paid s op 1) op index cell memory) op 2).host.gas.burnt = _
  rw [hd.1, hb.1, hp.1]; omega

theorem guardStore_memory (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (guardStore s op index cell memory).mems[index]? = some (writeI32 memory cell.toNat (nextCount memory cell)) := by
  let before := swapEntryStore (paid (incrementEntryStore (paid s op 1) op) op 10) op
  have hp : before.mems[index]? = some memory := by
    simpa only [before, swapEntryStore, incrementEntryStore, paid, chargedStore] using hm
  have h := swapStore_memory before op index cell (nextCount memory cell) memory hp
  simpa only [guardStore, calledIncrementStore, incrementStore, calledSwapStore, before, paid, chargedStore] using h

theorem guardStore_resources (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :
    {guardStore s op index cell memory with mems := s.mems, host := s.host} = s := by
  simp only [guardStore, calledIncrementStore, incrementStore, calledSwapStore, swapStore,
    incrementEntryStore, swapEntryStore, paid, chargedStore, storeI32]

theorem recordStore_gas (s : Store NearState) (op index rest : Nat) (out cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (8 * op + rest)) :
    (recordStore s op index out cell memory).host.gas.burnt = s.host.gas.burnt + 8 * op ∧
    (recordStore s op index out cell memory).host.gas.promises = s.host.gas.promises ∧
    (recordStore s op index out cell memory).host.gas.Credits rest := by
  have h3 := paid_gas s op 3 (5 * op + rest) (hc.mono (by omega))
  have c3 := paid_credits s op 3 (5 * op + rest) (hc.mono (by omega))
  have h5 := paid_gas (storeI32 (paid s op 3) index (out.toNat + 4) memory cell) op 5 rest c3
  have c5 := paid_credits (storeI32 (paid s op 3) index (out.toNat + 4) memory cell) op 5 rest c3
  refine ⟨?_, h5.2.trans h3.2, c5⟩
  change (paid (storeI32 (paid s op 3) index (out.toNat + 4) memory cell) op 5).host.gas.burnt = _
  rw [h5.1]
  change (paid s op 3).host.gas.burnt + 5 * op = _
  rw [h3.1]; omega

def reserved (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid s op 5) globalIndex (.i32 (sp - 16))
def acquireStore (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) : Store NearState :=
  setGlobal (paid (recordStore (guardStore (reserved s op globalIndex sp) op memoryIndex cell memory)
    op memoryIndex out cell (writeI32 memory cell.toNat (nextCount memory cell))) op 4) globalIndex (.i32 sp)
def acquireFrame (frame : CallFrame) (sp cell : UInt32) : CallFrame :=
  acquiredFrame {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))} cell

theorem recordStore_resources (s : Store NearState) (op index : Nat) (out cell : UInt32) (memory : Memory) :
    {recordStore s op index out cell memory with mems := s.mems, host := s.host} = s := by
  simp only [recordStore, storeI32, paid, chargedStore]

/-- Complete accepted f429 body. It increments the cell first, writes the
borrow record sequentially, and restores SP modulo 2^32. -/
theorem wp_acquire (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp out cell : UInt32) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (global : GlobalInst) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hcell : frame.locals[1]? = some (.i32 cell))
    (hsize : 5 ≤ frame.locals.size) (hlinks : Links s mi frame.inst)
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hsp : global.value = .i32 sp) (hmi : mi.memAddrs[0]? = some memoryIndex)
    (hmem : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hcb : cell.toNat + 4 ≤ memory.byteSize) (hob : out.toNat + 8 ≤ memory.byteSize)
    (haccept : Numeric.irelop32 .ge_s (nextCount memory cell) 1 = true) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (60 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (acquireStore s cfg.regularOpCost globalIndex memoryIndex sp out cell memory)
      limits base.toArray (acquireFrame frame sp cell) callers code)) rest post) :
    WP cfg (fuel + 45) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnAcquire.acquireBody ++ code))) (60 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let r := reserved s op globalIndex sp
  let g := guardStore r op memoryIndex cell memory
  let memory' := writeI32 memory cell.toNat (nextCount memory cell)
  let recorded := recordStore g op memoryIndex out cell memory'
  let f1 := {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))}
  let f2 := acquiredFrame f1 cell
  have hout1 : f1.locals[0]? = some (.i32 out) := by simpa [f1] using hout
  have hcell1 : f1.locals[1]? = some (.i32 cell) := by simpa [f1] using hcell
  have hout2 : f2.locals[0]? = some (.i32 out) := by simpa [f2, acquiredFrame] using hout1
  have hcell2 : f2.locals[1]? = some (.i32 cell) := by simpa [f2, acquiredFrame] using hcell1
  have hborrow : f2.locals[4]? = some (.i32 cell) := by
    simp [f2, acquiredFrame, f1, show 4 < frame.locals.size by omega]
  have hscratch : f2.locals[3]? = some (.i32 (sp - 16)) := by
    simp [f2, acquiredFrame, f1, show 3 < frame.locals.size by omega]
  have hr : r.host.gas.Credits (55 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have hg := guardStore_gas r op memoryIndex (12 * op + rest) cell memory (hr.mono (by omega))
  have hrec := recordStore_gas g op memoryIndex (4 * op + rest) out cell memory' (hg.2.2.mono (by omega))
  have hlinksR : Links r mi f1.inst := links_setGlobal _ mi frame.inst globalIndex (.i32 (sp - 16)) (links_paid s mi frame.inst op 5 hlinks)
  have hmemR : r.mems[memoryIndex]? = some memory := by simpa only [r, reserved, setGlobal, paid, chargedStore] using hmem
  have hmemG : g.mems[memoryIndex]? = some memory' := guardStore_memory r op memoryIndex cell memory hmemR
  have hgspec := writeI32_spec memory cell.toNat (nextCount memory cell) hwf hcb
  have hgr : r.globals[globalIndex]? = some {global with value := .i32 (sp - 16)} := by
    simp [r, reserved, setGlobal, paid, chargedStore, Array.getElem?_modify, hglobal]
  have gr := guardStore_resources r op memoryIndex cell memory
  have rr := recordStore_resources g op memoryIndex out cell memory'
  have hmG : g.modules[f2.inst]? = some mi := by
    have h := congrArg (fun t => t.modules[frame.inst]?) gr
    simpa only [g, f2, acquiredFrame, f1] using h.trans hlinksR.module
  have hmRec : recorded.modules[f2.inst]? = some mi := by
    have h := congrArg (fun t => t.modules[frame.inst]?) rr
    simpa only [recorded, f2, acquiredFrame, f1] using h.trans hmG
  have hgG : g.globals[globalIndex]? = some {global with value := .i32 (sp - 16)} := by
    simpa only [g] using (congrArg (fun t => t.globals[globalIndex]?) gr).trans hgr
  have hgRec : recorded.globals[globalIndex]? = some {global with value := .i32 (sp - 16)} := by
    simpa only [recorded] using (congrArg (fun t => t.globals[globalIndex]?) rr).trans hgG
  have hrestore := WNear.Proofs.ValueReturnBorrow.wp_restore cfg fuel rest recorded limits base.toArray f2 callers code mi globalIndex
    {global with value := .i32 (sp - 16)} (sp - 16) 3 post hscratch hmRec hgi hgRec hrec.2.2
  have hrestore' : WP cfg (fuel + 4) (.next (atCode recorded limits base.toArray f2 callers
      ([.local_get 3, .i32_const 16, .i32_binop .add, .global_set 0] ++ code))) (4 * op + rest) post := by
    apply hrestore
    simpa only [UInt32.sub_add_cancel, acquireStore, r, g, recorded, memory', f2, f1, acquireFrame, op] using hnext
  have hwrite := wp_record cfg (fuel + 4) (4 * op + rest) g limits base.toArray f2 callers
    ([.local_get 3, .i32_const 16, .i32_binop .add, .global_set 0] ++ code) out cell mi memoryIndex memory' post
    hout2 hcell2 hborrow hmG hmi hmemG hgspec.1 (by dsimp [memory']; rw [hgspec.2.1]; exact hob)
    (hg.2.2.mono (by omega))
  have hwrite' := hwrite hrestore'
  rw [show fuel + 4 + 8 = fuel + 12 by omega,
    show 8 * cfg.regularOpCost + (4 * op + rest) = 12 * op + rest by dsimp [op]; omega] at hwrite'
  have htail : WP cfg (fuel + 12) (.next (atCode g limits base.toArray f2 callers
      (WNear.Binary.ValueReturnAcquire.acquireTail ++ code))) (12 * op + rest) post := by
    simpa only [WNear.Binary.ValueReturnAcquire.acquireTail, List.cons_append, List.nil_append] using hwrite'
  have hguard := wp_acquireGuard cfg (fuel + 12) (12 * op + rest) r limits base f1 callers
    (WNear.Binary.ValueReturnAcquire.acquireTail ++ code) cell mi memoryIndex memory post hcell1
    (by simpa [f1] using hsize) hlinksR hmi hmemR hcb haccept hnonzero hdepth (hr.mono (by omega))
  have hguard' := hguard htail
  rw [show fuel + 12 + 27 = fuel + 39 by omega,
    show 43 * cfg.regularOpCost + (12 * op + rest) = 55 * op + rest by dsimp [op]; omega] at hguard'
  have hblock := wp_block_empty cfg (fuel + 39) (55 * op + rest) r limits base.toArray f1 callers
    (WNear.Binary.ValueReturnAcquire.acquireGuard ++ WNear.Binary.ValueReturnAcquire.acquirePanic)
    (WNear.Binary.ValueReturnAcquire.acquireTail ++ code) post hr
  have hguard'' : WP cfg (fuel + 39) (.next (atCode r limits base.toArray
      (emptyBlockFrame f1 base.toArray.size (WNear.Binary.ValueReturnAcquire.acquireTail ++ code)) callers
      (WNear.Binary.ValueReturnAcquire.acquireGuard ++ WNear.Binary.ValueReturnAcquire.acquirePanic)))
      (55 * op + rest) post := by simpa using hguard'
  have hblock' := hblock hguard''
  rw [show fuel + 39 + 1 = fuel + 40 by omega] at hblock'
  have hreserve := WNear.Proofs.ValueReturnBorrow.wp_reserve cfg (fuel + 40) (55 * op + rest) s limits base.toArray frame callers
    (.block .empty (WNear.Binary.ValueReturnAcquire.acquireGuard ++ WNear.Binary.ValueReturnAcquire.acquirePanic) ::
      (WNear.Binary.ValueReturnAcquire.acquireTail ++ code)) mi globalIndex global sp 3 post hlinks.module hgi hglobal hsp
    (hc.mono (by dsimp [op]; omega))
  have hentry := hreserve hblock'
  rw [show fuel + 40 + 5 = fuel + 45 by omega,
    show 5 * cfg.regularOpCost + (55 * op + rest) = 60 * cfg.regularOpCost + rest by dsimp [op]; omega] at hentry
  simpa only [WNear.Binary.ValueReturnAcquire.acquireBody, WNear.Binary.ValueReturnAcquire.acquirePrologue,
    List.append_assoc, List.cons_append, List.nil_append] using hentry

theorem acquireStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out cell : UInt32) (memory : Memory) (hc : s.host.gas.Credits (60 * op + rest)) :
    (acquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 60 * op ∧
    (acquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
    (acquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
  let r := reserved s op globalIndex sp
  let g := guardStore r op memoryIndex cell memory
  let recorded := recordStore g op memoryIndex out cell (writeI32 memory cell.toNat (nextCount memory cell))
  have h5 := paid_gas s op 5 (55 * op + rest) (hc.mono (by omega))
  have c5 : r.host.gas.Credits (55 * op + rest) := paid_credits s op 5 _ (hc.mono (by omega))
  have h43 := guardStore_gas r op memoryIndex (12 * op + rest) cell memory (c5.mono (by omega))
  have h8 := recordStore_gas g op memoryIndex (4 * op + rest) out cell
    (writeI32 memory cell.toNat (nextCount memory cell)) (h43.2.2.mono (by omega))
  have h4 := paid_gas recorded op 4 rest h8.2.2
  refine ⟨?_, h4.2.trans (h8.2.1.trans (h43.2.1.trans h5.2)), paid_credits recorded op 4 rest h8.2.2⟩
  change (paid recorded op 4).host.gas.burnt = _
  rw [h4.1, h8.1, h43.1]
  change (paid s op 5).host.gas.burnt + 43 * op + 8 * op + 4 * op = _
  rw [h5.1]; omega

def acquireEntryStore (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (11 * op)
def calledAcquireStore (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) : Store NearState := acquireStore (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory

/-- Actual direct f429 acquisition, with nested f494/f672 and return included.
The panic location is ignored on this accepted path. -/
theorem wp_call_acquire (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp out cell location : UInt32) (mi : ModuleInst)
    (functionAddress globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory) (post : Post)
    (hlinks : Links s mi frame.inst)
    (hfi : mi.funcAddrs[429]? = some functionAddress)
    (hfn : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnAcquire.acquireSignature frame.inst WNear.Binary.ValueReturnAcquire.acquireFunction))
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hsp : global.value = .i32 sp) (hmi : mi.memAddrs[0]? = some memoryIndex)
    (hmem : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hcb : cell.toNat + 4 ≤ memory.byteSize) (hob : out.toNat + 8 ≤ memory.byteSize)
    (haccept : Numeric.irelop32 .ge_s (nextCount memory cell) 1 = true) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 3 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (72 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledAcquireStore s cfg.regularOpCost globalIndex memoryIndex sp out cell memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 47) (.next (atCode s limits (base ++ [Value.i32 out, .i32 cell, .i32 location]).toArray
      frame callers (.call 429 :: code))) (72 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee : CallFrame :=
    {locals := #[.i32 out, .i32 cell, .i32 location, .i32 0, .i32 0]
     inst := frame.inst
     arity := 0
     height := base.length
     labels := []
     code := []}
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (71 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (60 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hl := links_charge _ mi frame.inst (11 * op) (links_charge s mi frame.inst op hlinks)
  have hmem' : (acquireEntryStore s op).mems[memoryIndex]? = some memory := hmem
  have hg' : (acquireEntryStore s op).globals[globalIndex]? = some global := hglobal
  have c := (acquireStore_gas (acquireEntryStore s op) op globalIndex memoryIndex rest sp out cell memory ha.2.2.2).2.2
  have hleave := wp_leave_wasm cfg fuel rest (calledAcquireStore s op globalIndex memoryIndex sp out cell memory)
    limits base [] (acquireFrame callee sp cell) saved callers post rfl rfl rfl c
  simp only [List.append_nil] at hleave
  have ht : WP cfg fuel (.next (atCode (calledAcquireStore s op globalIndex memoryIndex sp out cell memory)
      limits base.toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have hleave' := hleave ht
  have hbody := wp_acquire cfg (fuel + 1) rest (acquireEntryStore s op) limits base callee (saved :: callers) []
    sp out cell mi globalIndex memoryIndex global memory post rfl rfl (by simp [callee]) hl hgi hg' hsp hmi hmem' hwf hcb hob
    haccept hnonzero (by simpa using hdepth) ha.2.2.2
  have hbody' := hbody hleave'
  rw [show fuel + 1 + 45 = fuel + 46 by omega] at hbody'
  have he := wp_call_wasm cfg (fuel + 46) (60 * op + rest) s limits base [.i32 out, .i32 cell, .i32 location]
    frame callers code 429 functionAddress mi WNear.Binary.ValueReturnAcquire.acquireSignature frame.inst
    WNear.Binary.ValueReturnAcquire.acquireFunction post hlinks.module hfi hfn rfl (by omega)
  have hact : activationGas op (wasmLocals WNear.Binary.ValueReturnAcquire.acquireFunction [.i32 out, .i32 cell, .i32 location]) = 11 * op := by
    simp [wasmLocals, WNear.Binary.ValueReturnAcquire.acquireFunction, activationGas, ValType.default]
  rw [hact] at he
  have he' := he (hc.mono (by dsimp [op]; omega))
  have hbody'' : WP cfg (fuel + 46) (.next (wasmCallee (acquireEntryStore s op) limits base frame callers code
      WNear.Binary.ValueReturnAcquire.acquireSignature frame.inst WNear.Binary.ValueReturnAcquire.acquireFunction
      [.i32 out, .i32 cell, .i32 location])) (60 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.ValueReturnAcquire.acquireSignature,
      WNear.Binary.ValueReturnAcquire.acquireFunction, callee, saved, atCode, ValType.default, op] using hbody'
  have hall := he' hbody''
  rw [show fuel + 46 + 1 = fuel + 47 by omega,
    show cfg.regularOpCost + (11 * op + (60 * op + rest)) = 72 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  exact hall

theorem calledAcquireStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out cell : UInt32) (memory : Memory) (hc : s.host.gas.Credits (72 * op + rest)) :
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 72 * op ∧
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (71 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (60 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hb := acquireStore_gas (acquireEntryStore s op) op globalIndex memoryIndex rest sp out cell memory ha.2.2.2
  refine ⟨?_, hb.2.1.trans (ha.2.2.1.trans hop.2.2.1), hb.2.2⟩
  change (acquireStore (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory).host.gas.burnt = _
  rw [hb.1]
  have he : (acquireEntryStore s op).host.gas.burnt = s.host.gas.burnt + op + 11 * op :=
    ha.2.1.trans (by rw [show (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op from hop.2.1])
  rw [he]; omega

theorem recordStore_memory (s : Store NearState) (op index : Nat) (out cell : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (recordStore s op index out cell memory).mems[index]? = some (recordMemory memory out cell) := by
  have hfirst : (storeI32 (paid s op 3) index (out.toNat + 4) memory cell).mems[index]? =
      some (writeI32 memory (out.toNat + 4) cell) := by
    apply storeI32_memory
    simpa only [paid, chargedStore] using hm
  have hpaid : (paid (storeI32 (paid s op 3) index (out.toNat + 4) memory cell) op 5).mems[index]? =
      some (writeI32 memory (out.toNat + 4) cell) := by
    simpa only [paid, chargedStore] using hfirst
  exact storeI32_memory _ index out.toNat _ (cell + 4) hpaid

theorem acquireStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (hm : s.mems[memoryIndex]? = some memory) :
    (acquireStore s op globalIndex memoryIndex sp out cell memory).mems[memoryIndex]? =
      some (recordMemory (writeI32 memory cell.toNat (nextCount memory cell)) out cell) := by
  let r := reserved s op globalIndex sp
  have hr : r.mems[memoryIndex]? = some memory := by simpa only [r, reserved, setGlobal, paid, chargedStore] using hm
  have hg := guardStore_memory r op memoryIndex cell memory hr
  have h := recordStore_memory (guardStore r op memoryIndex cell memory) op memoryIndex out cell
    (writeI32 memory cell.toNat (nextCount memory cell)) hg
  simpa only [acquireStore, setGlobal, paid, chargedStore, r] using h

theorem acquireStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (global : GlobalInst) (hg : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    (acquireStore s op globalIndex memoryIndex sp out cell memory).globals = s.globals := by
  let r := reserved s op globalIndex sp
  let g := guardStore r op memoryIndex cell memory
  let recorded := recordStore g op memoryIndex out cell (writeI32 memory cell.toNat (nextCount memory cell))
  have hgg : g.globals = r.globals := by
    simpa only [g] using congrArg (fun t => t.globals) (guardStore_resources r op memoryIndex cell memory)
  have hrg : recorded.globals = g.globals := by
    simpa only [recorded] using congrArg (fun t => t.globals)
      (recordStore_resources g op memoryIndex out cell (writeI32 memory cell.toNat (nextCount memory cell)))
  have hrestore := WNear.Proofs.StorePairCaller.setGlobal_restore s globalIndex (.i32 (sp - 16)) global hg
  have h := congrArg (fun arr => arr.modify globalIndex (fun x => {x with value := .i32 sp})) (hrg.trans hgg)
  have h' : (acquireStore s op globalIndex memoryIndex sp out cell memory).globals =
      (setGlobal r globalIndex (.i32 sp)).globals := by
    simpa only [acquireStore, paid, chargedStore, setGlobal, recorded, g, r] using h
  rw [h']
  simpa only [r, reserved, setGlobal, paid, chargedStore, hsp] using hrestore

/-- Apart from the three sequential bounded writes and internal gas/profile,
all guest store fields are preserved, including the whole original globals. -/
theorem acquireStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (global : GlobalInst) (hg : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    {acquireStore s op globalIndex memoryIndex sp out cell memory with mems := s.mems, host := s.host} = s := by
  have h := acquireStore_globals s op globalIndex memoryIndex sp out cell memory global hg hsp
  cases s
  simp_all only [acquireStore, reserved, recordStore, guardStore, calledIncrementStore, incrementStore,
    calledSwapStore, swapStore, incrementEntryStore, swapEntryStore, paid, chargedStore, setGlobal, storeI32]

theorem calledAcquireStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (global : GlobalInst) (hg : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    {calledAcquireStore s op globalIndex memoryIndex sp out cell memory with mems := s.mems, host := s.host} = s := by
  have h := acquireStore_resources (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory global hg hsp
  have h' := congrArg (fun t : Store NearState => {t with host := s.host}) h
  simpa only [calledAcquireStore, acquireEntryStore, chargedStore] using h'

theorem calledAcquireStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (hm : s.mems[memoryIndex]? = some memory) :
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).mems[memoryIndex]? =
      some (recordMemory (writeI32 memory cell.toNat (nextCount memory cell)) out cell) :=
  acquireStore_memory (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory hm

theorem calledAcquireStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp out cell : UInt32)
    (memory : Memory) (global : GlobalInst) (hg : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).globals = s.globals :=
  acquireStore_globals (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory global hg hsp

end WNear.Proofs.ValueReturnAcquire
