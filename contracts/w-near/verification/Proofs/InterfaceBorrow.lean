import Proofs.InterfaceBorrowState
import Proofs.ValueReturnAcquire
import Proofs.ValueReturnOuter
import NearVM.MeteredLoopRules

namespace WNear.Proofs.InterfaceBorrow
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
open WNear.Proofs.ValueReturnBorrowCounters (calledSwapStore calledSwapStore_credits calledSwapStore_gas swapEntryStore swapStore swapStore_memory wp_call_swap)
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
/-- f492's tail invokes the actual swap helper, locks the counter and records its cell pointer. -/
theorem wp_takeTail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi calleeModule : ModuleInst)
    (functionAddress inst index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell)) (_hsize : 2 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hfindex : mi.funcAddrs[672]? = some functionAddress)
    (hf : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcm : s.modules[inst]? = some calleeModule) (hcmi : calleeModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (23 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (paid (calledSwapStore (paid s cfg.regularOpCost 2) cfg.regularOpCost index cell 4294967295 memory) cfg.regularOpCost 3)
      limits base.toArray (takeFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 14) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceBorrow.takeTail ++ code))) (23 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 2
  let swapped := calledSwapStore prepared op index cell 4294967295 memory
  have cp : prepared.host.gas.Credits (21 * op + rest) := paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  have cs : swapped.host.gas.Credits (3 * op + rest) := calledSwapStore_credits prepared op index _ cell 4294967295 memory (cp.mono (by omega))
  have hset := wp_local_set cfg fuel rest (paid swapped op 2) limits base.toArray frame callers code 1 (.i32 cell) post
    (paid_credits swapped op 2 _ (cs.mono (by omega))) hnext
  have hget := wp_local_get cfg (fuel + 1) (op + rest) (paid swapped op 1) limits base.toArray frame callers
    (.local_set 1 :: code) 0 (.i32 cell) post hcell (paid_credits swapped op 1 _ (cs.mono (by omega))) hset
  have hdrop := wp_drop cfg (fuel + 2) (2 * op + rest) swapped limits base.toArray frame callers (.local_get 0 :: .local_set 1 :: code)
    (.i32 (readI32 memory cell.toNat)) post (cs.mono (by omega))
  have hget' : WP cfg (fuel + 2) (.next (atCode (chargedStore swapped cfg.regularOpCost) limits base.toArray frame callers (.local_get 0 :: .local_set 1 :: code))) (2 * op + rest) post := by
    rw [show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at hget
    simpa only [paid, op, Nat.add_assoc, Nat.reduceAdd] using hget
  have hdrop' := hdrop hget'
  rw [show fuel + 2 + 1 = fuel + 3 by omega,
    show cfg.regularOpCost + (2 * op + rest) = 3 * op + rest by dsimp [op]; omega] at hdrop'
  have hm2 : prepared.modules[frame.inst]? = some mi := by simpa only [prepared, paid, chargedStore] using hm
  have hf2 : prepared.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction) := by
    simpa only [prepared, paid, chargedStore] using hf
  have hcm2 : prepared.modules[inst]? = some calleeModule := by simpa only [prepared, paid, chargedStore] using hcm
  have hmem2 : prepared.mems[index]? = some memory := by simpa only [prepared, paid, chargedStore] using hmem
  have hcall := wp_call_swap cfg (fuel + 3) (3 * op + rest) prepared limits base frame callers
    (.drop :: .local_get 0 :: .local_set 1 :: code) cell 4294967295 mi calleeModule functionAddress inst index memory post
    hm2 hfindex hf2 hcm2 hcmi hmem2 hb hdepth (cp.mono (by omega))
  have ht : WP cfg (fuel + 3) (.next (atCode swapped limits
      (base ++ [Value.i32 (readI32 memory cell.toNat)]).toArray frame callers (.drop :: .local_get 0 :: .local_set 1 :: code)))
      (3 * op + rest) post := by
    simpa using hdrop'
  have hcall' := hcall ht
  rw [show fuel + 3 + 9 = fuel + 12 by omega,
    show 18 * cfg.regularOpCost + (3 * op + rest) = 21 * op + rest by dsimp [op]; omega] at hcall'
  have hcall'' : WP cfg (fuel + 12) (.next (atCode prepared limits
      ((base.toArray.push (.i32 cell)).push (.i32 4294967295)) frame callers (.call 672 :: .drop :: .local_get 0 :: .local_set 1 :: code)))
      (21 * op + rest) post := by simpa using hcall'
  rw [show 23 * cfg.regularOpCost + rest = cfg.regularOpCost + (22 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 13) _ s limits base.toArray frame callers _ 0 (.i32 cell) post hcell (hc.mono (by omega))
  rw [show 22 * cfg.regularOpCost + rest = cfg.regularOpCost + (21 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 12) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 4294967295 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  · exact hcall''


/-- Accepted exclusive acquisition: the actual zero guard, sentinel swap and
block fallthrough, preserving every caller continuation. -/
theorem wp_take (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi calleeModule : ModuleInst)
    (functionAddress inst index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell)) (hsize : 2 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hfindex : mi.funcAddrs[672]? = some functionAddress)
    (hf : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction))
    (hcm : s.modules[inst]? = some calleeModule) (hcmi : calleeModule.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (hzero : readI32 memory cell.toNat = 0)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (29 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (takeStore s cfg.regularOpCost index cell memory) limits
      (base.toArray.push (.i32 cell)) (takeFrame (takeFrame frame 0) cell) callers code)) rest post) :
    WP cfg (fuel + 22) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceBorrow.takeBody ++ code))) (29 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let initialized := takeFrame frame 0
  let finished := takeFrame initialized cell
  let endcode := .local_get 1 :: code
  let block := emptyBlockFrame initialized base.length endcode
  let checked := paid s op 5
  let swapped := calledSwapStore (paid checked op 2) op index cell 4294967295 memory
  let final := paid swapped op 4
  have hci : initialized.locals[0]? = some (.i32 cell) := by simpa [initialized, takeFrame] using hcell
  have hcf : finished.locals[1]? = some (.i32 cell) := by simp [finished, takeFrame, initialized, show 1 < frame.locals.size by omega]
  have cp := paid_credits s op 7 (22 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cs : swapped.host.gas.Credits (4 * op + rest) := by
    apply calledSwapStore_credits
    simpa only [checked, ValueReturnBorrow.paid_add, Nat.reduceAdd] using cp.mono (show 18 * op + (4 * op + rest) ≤ 22 * op + rest by omega)
  have cmid := paid_credits swapped op 3 (op + rest) (cs.mono (by omega))
  have getRule := wp_local_get cfg fuel rest (paid swapped op 3) limits base.toArray finished callers code 1 (.i32 cell) post hcf cmid
  have getNext := getRule (by simpa only [final, takeStore, swapped, checked, finished, initialized, paid, ← ValueReturnBorrow.paid_add, Nat.reduceAdd, op] using hnext)
  have endRule := wp_end_label cfg (fuel + 1) (op + rest) (paid swapped op 3) limits base.toArray finished callers
    {arity := 0, height := base.length, rest := endcode, loop := none} post cmid
  have endNext := endRule getNext
  have hmf : checked.modules[block.inst]? = some mi := by simpa only [checked, block, initialized, emptyBlockFrame, takeFrame, paid, chargedStore] using hm
  have hff : checked.funcs[functionAddress]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction) := by simpa only [checked, paid, chargedStore] using hf
  have hcmf : checked.modules[inst]? = some calleeModule := by simpa only [checked, paid, chargedStore] using hcm
  have hmemf : checked.mems[index]? = some memory := by simpa only [checked, paid, chargedStore] using hmem
  have cchecked : checked.host.gas.Credits (24 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have tailRule := wp_takeTail cfg (fuel + 2) (op + rest) checked limits base block callers [] cell mi calleeModule
    functionAddress inst index memory post hci (by simpa [block, initialized, emptyBlockFrame, takeFrame] using hsize)
    hmf hfindex hff hcmf hcmi hmemf hb hdepth (cchecked.mono (by dsimp [op]; omega))
  have tailNext : WP cfg (fuel + 2) (.next (atCode (paid swapped op 3) limits base.toArray
      (takeFrame block cell) callers [])) (op + rest) post := by
    simpa only [block, finished, endcode, emptyBlockFrame, takeFrame, atCode, List.size_toArray] using endNext
  have tail := tailRule tailNext
  have hloadm : (paid s op 3).modules[block.inst]? = some mi := by simpa only [paid, chargedStore, block, initialized, takeFrame, emptyBlockFrame] using hm
  have hloadmem : (paid s op 3).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have branchRule := wp_br_if_zero cfg (fuel + 16) (24 * op + rest) (paid s op 4) limits base.toArray block callers
    WNear.Binary.InterfaceBorrow.takeTail 0 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega)))
  rw [show 23 * cfg.regularOpCost + (op + rest) = 24 * op + rest by dsimp [op]; omega] at tail
  have branchNext := branchRule (by simpa only [checked, paid, op, Nat.add_assoc, Nat.reduceAdd, List.append_nil] using tail)
  have loadRule := wp_i32_load cfg (fuel + 17) (25 * op + rest) (paid s op 3) limits base.toArray block callers
    ( .br_if 0 :: WNear.Binary.InterfaceBorrow.takeTail) {align := 2, offset := 0} cell mi index memory post
    hloadm hi hloadmem (by simpa using hb) (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega)))
  rw [show cfg.regularOpCost + (24 * op + rest) = 25 * op + rest by dsimp [op]; omega] at branchNext
  have loadNext := loadRule (by simpa only [hzero, Nat.add_zero, paid, op, Nat.add_assoc, Nat.reduceAdd] using branchNext)
  have cellRule := wp_local_get cfg (fuel + 18) (26 * op + rest) (paid s op 2) limits base.toArray block callers
    (.load .i32 none {align := 2, offset := 0} :: .br_if 0 :: WNear.Binary.InterfaceBorrow.takeTail) 0 (.i32 cell) post hci
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega)))
  rw [show cfg.regularOpCost + (25 * op + rest) = 26 * op + rest by dsimp [op]; omega] at loadNext
  have cellNext := cellRule (by simpa only [paid, op, Nat.add_assoc, Nat.reduceAdd] using loadNext)
  have blockRule := wp_block_empty cfg (fuel + 19) (27 * op + rest) (paid s op 2) limits base.toArray initialized callers
    (WNear.Binary.InterfaceBorrow.takeGuard ++ WNear.Binary.InterfaceBorrow.takeTail) endcode post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega)))
  rw [show cfg.regularOpCost + (26 * op + rest) = 27 * op + rest by dsimp [op]; omega] at cellNext
  have blockNext := blockRule (by simpa only [WNear.Binary.InterfaceBorrow.takeGuard, List.cons_append, List.nil_append, block, List.size_toArray, op] using cellNext)
  have setRule := wp_local_set cfg (fuel + 20) (27 * op + rest) (paid s op 1) limits base.toArray frame callers
    (.block .empty (WNear.Binary.InterfaceBorrow.takeGuard ++ WNear.Binary.InterfaceBorrow.takeTail) :: endcode) 1 (.i32 0) post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have setNext := setRule (by simpa only [initialized, takeFrame, paid, op, Nat.add_assoc, Nat.reduceAdd] using blockNext)
  have constRule := wp_i32_const cfg (fuel + 21) (28 * op + rest) s limits base.toArray frame callers
    (.local_set 1 :: .block .empty (WNear.Binary.InterfaceBorrow.takeGuard ++ WNear.Binary.InterfaceBorrow.takeTail) :: endcode) 0 post
    (hc.mono (by dsimp [op]; omega))
  rw [show cfg.regularOpCost + (27 * op + rest) = 28 * op + rest by dsimp [op]; omega] at setNext
  have result := constRule (by simpa only [paid, op, Nat.add_assoc, Nat.reduceAdd] using setNext)
  rw [show cfg.regularOpCost + (28 * op + rest) = 29 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.InterfaceBorrow.takeBody, WNear.Binary.InterfaceBorrow.takeInit, List.cons_append, List.nil_append, endcode, Nat.add_assoc, Nat.reduceAdd] using result

/-- Primitive same-module links for the actual two deployed counter helpers. -/
structure Links (s : Store NearState) (mi : ModuleInst) (inst : Nat) : Prop where
  module : s.modules[inst]? = some mi
  swap : ∃ address, mi.funcAddrs[672]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  take : ∃ address, mi.funcAddrs[492]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.InterfaceBorrow.takeSignature inst WNear.Binary.InterfaceBorrow.takeFunction)

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

theorem takeStore_gas (s : Store NearState) (op index rest : Nat) (cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (29 * op + rest)) :
    (takeStore s op index cell memory).host.gas.burnt = s.host.gas.burnt + 29 * op ∧
    (takeStore s op index cell memory).host.gas.promises = s.host.gas.promises ∧
    (takeStore s op index cell memory).host.gas.Credits rest := by
  let prepared := paid s op 7
  let swapped := calledSwapStore prepared op index cell (4294967295) memory
  have cp : prepared.host.gas.Credits (22 * op + rest) := paid_credits s op 7 _ (hc.mono (by omega))
  have hp := paid_gas s op 7 (22 * op + rest) (hc.mono (by omega))
  have hs := calledSwapStore_gas prepared op index (4 * op + rest) cell (4294967295) memory (cp.mono (by omega))
  have cs : swapped.host.gas.Credits (4 * op + rest) := calledSwapStore_credits prepared op index _ cell (4294967295) memory (cp.mono (by omega))
  have hd := paid_gas swapped op 4 rest cs
  refine ⟨?_, hd.2.trans (hs.2.trans hp.2), paid_credits swapped op 4 rest cs⟩
  change (paid swapped op 4).host.gas.burnt = _
  rw [hd.1, hs.1, hp.1]; omega

/-- Actual direct f492 call; primitive links fix the callee, with no assumed
execution result. The activation, nested swap and final return are included. -/
theorem wp_call_take (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlinks : Links s mi frame.inst) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (haccept : readI32 memory cell.toNat = 0)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (39 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledTakeStore s cfg.regularOpCost index cell memory) limits
      (base ++ [Value.i32 cell]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 24) (.next (atCode s limits (base ++ [Value.i32 cell]).toArray frame callers
      (.call 492 :: code))) (39 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee : CallFrame :=
    {locals := #[.i32 cell, .i32 0]
     inst := frame.inst
     arity := 1
     height := base.length
     labels := []
     code := []}
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (38 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (9 * op) (29 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hl := links_charge _ mi frame.inst (9 * op) (links_charge s mi frame.inst op hlinks)
  have hmem' : (takeEntryStore s op).mems[index]? = some memory := by simpa only [takeEntryStore, chargedStore] using hmem
  have c := (takeStore_gas (takeEntryStore s op) op index rest cell memory (ha.2.2.2.mono (by omega))).2.2
  have hleave := wp_leave_wasm cfg fuel rest (calledTakeStore s op index cell memory) limits base [.i32 cell]
    (takeFrame (takeFrame callee 0) cell) saved callers post rfl rfl rfl c
  have ht : WP cfg fuel (.next (atCode (calledTakeStore s op index cell memory) limits
      (base ++ [Value.i32 cell]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have hleave' := hleave ht
  have hleave'' : WP cfg (fuel + 1) (.next (atCode (calledTakeStore s op index cell memory) limits
      (base.toArray.push (.i32 cell)) (takeFrame (takeFrame callee 0) cell) (saved :: callers) [])) rest post := by
    simpa using hleave'
  rcases hl.swap with ⟨swapAddress, hsa, hsf⟩
  have hbody := wp_take cfg (fuel + 1) rest (takeEntryStore s op) limits base callee (saved :: callers) [] cell
    mi mi swapAddress frame.inst index memory post rfl (by simp [callee]) hl.module hi hsa hsf hl.module hi hmem' hb haccept (by simpa using hdepth) ha.2.2.2
  have hbody' := hbody hleave''
  rw [show fuel + 1 + 22 = fuel + 23 by omega] at hbody'
  rcases hlinks.take with ⟨address, had, hfn⟩
  have he := wp_call_wasm cfg (fuel + 23) (29 * op + rest) s limits base [.i32 cell] frame callers code 492 address
    mi WNear.Binary.InterfaceBorrow.takeSignature frame.inst WNear.Binary.InterfaceBorrow.takeFunction
    post hlinks.module had hfn rfl (by omega)
  have hact : activationGas op (wasmLocals WNear.Binary.InterfaceBorrow.takeFunction [.i32 cell]) = 9 * op := by
    simp [wasmLocals, WNear.Binary.InterfaceBorrow.takeFunction, activationGas, ValType.default]
  rw [hact] at he
  have he' := he (hc.mono (by dsimp [op]; omega))
  have hbody'' : WP cfg (fuel + 23) (.next (wasmCallee (takeEntryStore s op) limits base frame callers code
      WNear.Binary.InterfaceBorrow.takeSignature frame.inst WNear.Binary.InterfaceBorrow.takeFunction [.i32 cell]))
      (29 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.InterfaceBorrow.takeSignature,
      WNear.Binary.InterfaceBorrow.takeFunction, WNear.Binary.ValueReturnAcquire.incrementSignature, callee, saved, atCode, ValType.default, op] using hbody'
  have hall := he' hbody''
  rw [show fuel + 23 + 1 = fuel + 24 by omega,
    show cfg.regularOpCost + (9 * op + (29 * op + rest)) = 39 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  exact hall


theorem calledTakeStore_gas (s : Store NearState) (op index rest : Nat) (cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (39 * op + rest)) :
    (calledTakeStore s op index cell memory).host.gas.burnt = s.host.gas.burnt + 39 * op ∧
    (calledTakeStore s op index cell memory).host.gas.promises = s.host.gas.promises ∧
    (calledTakeStore s op index cell memory).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (38 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (9 * op) (29 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hb := takeStore_gas (takeEntryStore s op) op index rest cell memory ha.2.2.2
  refine ⟨?_, hb.2.1.trans (ha.2.2.1.trans hop.2.2.1), hb.2.2⟩
  change (takeStore (takeEntryStore s op) op index cell memory).host.gas.burnt = _
  rw [hb.1]
  have he : (takeEntryStore s op).host.gas.burnt = s.host.gas.burnt + op + 9 * op :=
    ha.2.1.trans (by rw [show (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op from hop.2.1])
  rw [he]; omega

theorem guardStore_gas (s : Store NearState) (op index rest : Nat) (cell : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (42 * op + rest)) :
    (guardStore s op index cell memory).host.gas.burnt = s.host.gas.burnt + 42 * op ∧
    (guardStore s op index cell memory).host.gas.promises = s.host.gas.promises ∧
    (guardStore s op index cell memory).host.gas.Credits rest := by
  have cp := paid_credits s op 1 (41 * op + rest) (hc.mono (by omega))
  have hp := paid_gas s op 1 (41 * op + rest) (hc.mono (by omega))
  have hb := calledTakeStore_gas (paid s op 1) op index (2 * op + rest) cell memory (cp.mono (by omega))
  have hd := paid_gas (calledTakeStore (paid s op 1) op index cell memory) op 2 rest hb.2.2
  refine ⟨?_, hd.2.trans (hb.2.1.trans hp.2), paid_credits _ op 2 rest hb.2.2⟩
  change (paid (calledTakeStore (paid s op 1) op index cell memory) op 2).host.gas.burnt = _
  rw [hd.1, hb.1, hp.1]; omega

theorem guardStore_memory (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (guardStore s op index cell memory).mems[index]? = some (writeI32 memory cell.toNat (4294967295)) := by
  let before := swapEntryStore (paid (takeEntryStore (paid s op 1) op) op 7) op
  have hp : before.mems[index]? = some memory := by
    simpa only [before, swapEntryStore, takeEntryStore, paid, chargedStore] using hm
  have h := swapStore_memory before op index cell (4294967295) memory hp
  simpa only [guardStore, calledTakeStore, takeStore, calledSwapStore, before, takeEntryStore, swapEntryStore, swapStore, paid, chargedStore, storeI32] using h

theorem guardStore_resources (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :
    {guardStore s op index cell memory with mems := s.mems, host := s.host} = s := by
  simp only [guardStore, calledTakeStore, takeStore, calledSwapStore, swapStore,
    takeEntryStore, swapEntryStore, paid, chargedStore, storeI32]

/-- The actual f441 block invokes f492 and branches over panic precisely when
its accepted result is nonzero. Its complete nested call is proved above. -/
theorem wp_acquireGuard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hcell : frame.locals[1]? = some (.i32 cell)) (_hsize : 5 ≤ frame.locals.size)
    (hlinks : Links s mi frame.inst) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : cell.toNat + 4 ≤ memory.byteSize)
    (haccept : readI32 memory cell.toNat = 0) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (42 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (guardStore s cfg.regularOpCost index cell memory) limits
      base.toArray (acquiredFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 27) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.length code) callers
      (WNear.Binary.InterfaceBorrow.acquireGuard ++ WNear.Binary.InterfaceBorrow.acquirePanic)))
      (42 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let block := emptyBlockFrame frame base.length code
  let frame' := acquiredFrame frame cell
  let borrowed := calledTakeStore (paid s op 1) op index cell memory
  have cp : (paid s op 1).host.gas.Credits (41 * op + rest) := paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  have hop := GasCounter.burn_credits (paid s op 1).host.gas op (40 * op + rest) (cp.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore (paid s op 1) op).host.gas (9 * op) (31 * op + rest)
    (hop.2.2.2.mono (by omega))
  have cb : borrowed.host.gas.Credits (2 * op + rest) :=
    (takeStore_gas (takeEntryStore (paid s op 1) op) op index (2 * op + rest) cell memory (ha.2.2.2.mono (by omega))).2.2
  have hbr := wp_br_if_block_nonzero cfg fuel rest (paid borrowed op 1) limits base.toArray frame' callers code
    WNear.Binary.InterfaceBorrow.acquirePanic cell post hnonzero
    (paid_credits borrowed op 1 _ (cb.mono (by omega))) hnext
  have htee := wp_local_tee cfg (fuel + 1) (op + rest) borrowed limits base.toArray block callers
    (.br_if 0 :: WNear.Binary.InterfaceBorrow.acquirePanic) 4 (.i32 cell) post (cb.mono (by omega))
  have hbr' : WP cfg (fuel + 1) (.next (atCode (paid borrowed op 1) limits (base.toArray.push (.i32 cell))
      {block with locals := block.locals.set! 4 (.i32 cell)} callers (.br_if 0 :: WNear.Binary.InterfaceBorrow.acquirePanic)))
      (op + rest) post := by
    simpa [block, frame', acquiredFrame, ValueReturnAcquire.acquiredFrame, emptyBlockFrame, op] using hbr
  simp only [paid] at hbr'
  have htee' := htee hbr'
  rw [show fuel + 1 + 1 = fuel + 2 by omega,
    show cfg.regularOpCost + (op + rest) = 2 * op + rest by dsimp [op]; omega] at htee'
  have hl : Links (paid s op 1) mi block.inst := links_paid s mi frame.inst op 1 hlinks
  have hm1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hcall := wp_call_take cfg (fuel + 2) (2 * op + rest) (paid s op 1) limits base block callers
    (.local_tee 4 :: .br_if 0 :: WNear.Binary.InterfaceBorrow.acquirePanic) cell mi index memory post
    hl hi hm1 hb haccept hdepth (cp.mono (by omega))
  have htee'' : WP cfg (fuel + 2) (.next (atCode borrowed limits (base ++ [Value.i32 cell]).toArray block callers
      (.local_tee 4 :: .br_if 0 :: WNear.Binary.InterfaceBorrow.acquirePanic))) (2 * op + rest) post := by
    simpa using htee'
  have hcall' := hcall htee''
  rw [show fuel + 2 + 24 = fuel + 26 by omega,
    show 39 * cfg.regularOpCost + (2 * op + rest) = 41 * op + rest by dsimp [op]; omega] at hcall'
  have hget := wp_local_get cfg (fuel + 26) (41 * op + rest) s limits base.toArray block callers
    (.call 492 :: .local_tee 4 :: .br_if 0 :: WNear.Binary.InterfaceBorrow.acquirePanic) 1 (.i32 cell) post hcell
    (hc.mono (by dsimp [op]; omega))
  have hcall'' : WP cfg (fuel + 26) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 cell)) block callers
      (.call 492 :: .local_tee 4 :: .br_if 0 :: WNear.Binary.InterfaceBorrow.acquirePanic))) (41 * op + rest) post := by
    simpa using hcall'
  have hall := hget hcall''
  rw [show fuel + 26 + 1 = fuel + 27 by omega,
    show cfg.regularOpCost + (41 * op + rest) = 42 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  simpa only [WNear.Binary.InterfaceBorrow.acquireGuard, List.cons_append, List.nil_append] using hall

/-- Actual sequential record writes. They use the already locked counter memory;
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

theorem recordStore_resources (s : Store NearState) (op index : Nat) (out cell : UInt32) (memory : Memory) :
    {recordStore s op index out cell memory with mems := s.mems, host := s.host} = s := by
  simp only [recordStore, storeI32, paid, chargedStore]


end WNear.Proofs.InterfaceBorrow
