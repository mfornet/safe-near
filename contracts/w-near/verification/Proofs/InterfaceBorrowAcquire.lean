import Proofs.InterfaceBorrowAcquireTail

/-! Actual accepted f441 acquisition, composed from independently checked phases. -/
namespace WNear.Proofs.InterfaceBorrow
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

def acquireGuardTailStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out cell : UInt32) (memory : Memory) : Store NearState :=
  acquireTailStore (guardStore s op memoryIndex cell memory) op globalIndex memoryIndex sp out cell
    (writeI32 memory cell.toNat 4294967295)

/-- The real nested guard followed by the twelve-instruction record/restore tail,
with the shadow-stack reservation still abstract. -/
theorem wp_acquireGuardTail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp out cell : UInt32) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (global : GlobalInst) (memory : Memory) (post : Post)
    (hout : frame.locals[0]? = some (.i32 out)) (hcell : frame.locals[1]? = some (.i32 cell))
    (hscratch : frame.locals[3]? = some (.i32 (sp - 16))) (hsize : 5 ≤ frame.locals.size)
    (hlinks : Links s mi frame.inst)
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hmi : mi.memAddrs[0]? = some memoryIndex)
    (hmem : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hcb : cell.toNat + 4 ≤ memory.byteSize) (hob : out.toNat + 8 ≤ memory.byteSize)
    (haccept : readI32 memory cell.toNat = 0) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (54 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (acquireGuardTailStore s cfg.regularOpCost globalIndex memoryIndex sp out cell memory)
      limits base.toArray (acquiredFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 39) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.length (WNear.Binary.ValueReturnAcquire.acquireTail ++ code)) callers
      (WNear.Binary.InterfaceBorrow.acquireGuard ++ WNear.Binary.InterfaceBorrow.acquirePanic)))
      (54 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let guarded := guardStore s op memoryIndex cell memory
  let memory' := writeI32 memory cell.toNat 4294967295
  let frame' := acquiredFrame frame cell
  have hout' : frame'.locals[0]? = some (.i32 out) := by simpa [frame', acquiredFrame] using hout
  have hcell' : frame'.locals[1]? = some (.i32 cell) := by simpa [frame', acquiredFrame] using hcell
  have hborrow : frame'.locals[4]? = some (.i32 cell) := by simp [frame', acquiredFrame, show 4 < frame.locals.size by omega]
  have hscratch' : frame'.locals[3]? = some (.i32 (sp - 16)) := by simpa [frame', acquiredFrame] using hscratch
  have gas := guardStore_gas s op memoryIndex (12 * op + rest) cell memory (hc.mono (by dsimp [op]; omega))
  have resources := guardStore_resources s op memoryIndex cell memory
  have hm : guarded.modules[frame'.inst]? = some mi := by
    have projection := congrArg (fun t => t.modules[frame.inst]?) resources
    simp only at projection
    have original := hlinks.module
    rw [← projection] at original
    simpa only [guarded, frame', acquiredFrame] using original
  have hg : guarded.globals[globalIndex]? = some global := by
    have projection := congrArg (fun t => t.globals[globalIndex]?) resources
    simp only at projection
    rw [← projection] at hglobal
    exact hglobal
  have hmemory : guarded.mems[memoryIndex]? = some memory' := guardStore_memory s op memoryIndex cell memory hmem
  have spec := writeI32_spec memory cell.toNat 4294967295 hwf hcb
  have bound : out.toNat + 8 ≤ memory'.byteSize := by simpa only [memory', spec.2.1] using hob
  have tailRule := wp_acquireTail cfg fuel rest guarded limits base.toArray frame' callers code sp out cell mi
    globalIndex memoryIndex global memory' post hout' hcell' hborrow hscratch' hm hgi hg hmi hmemory spec.1 bound gas.2.2
  have tailNext : WP cfg fuel (.next (atCode (acquireTailStore guarded op globalIndex memoryIndex sp out cell memory')
      limits base.toArray frame' callers code)) rest post := by
    simpa only [acquireGuardTailStore, guarded, memory', frame', op] using hnext
  have tail := tailRule tailNext
  have guardRule := wp_acquireGuard cfg (fuel + 12) (12 * op + rest) s limits base frame callers
    (WNear.Binary.ValueReturnAcquire.acquireTail ++ code) cell mi memoryIndex memory post hcell hsize hlinks hmi hmem hcb
    haccept hnonzero hdepth (hc.mono (by dsimp [op]; omega))
  have result := guardRule tail
  rw [show 42 * cfg.regularOpCost + (12 * op + rest) = 54 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

/-- Complete accepted f441 body, including the real f492/f672 calls. There is
no stack-address bound: its shadow SP arithmetic wraps modulo 2^32. -/
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
    (haccept : readI32 memory cell.toNat = 0) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (59 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (acquireStore s cfg.regularOpCost globalIndex memoryIndex sp out cell memory)
      limits base.toArray (acquireFrame frame sp cell) callers code)) rest post) :
    WP cfg (fuel + 45) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceBorrow.acquireBody ++ code))) (59 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let r := reserved s op globalIndex sp
  let f := {frame with locals := frame.locals.set! 3 (.i32 (sp - 16))}
  let tailCode := WNear.Binary.ValueReturnAcquire.acquireTail ++ code
  have hout' : f.locals[0]? = some (.i32 out) := by simpa [f] using hout
  have hcell' : f.locals[1]? = some (.i32 cell) := by simpa [f] using hcell
  have hscratch : f.locals[3]? = some (.i32 (sp - 16)) := by simp [f, show 3 < frame.locals.size by omega]
  have hsize' : 5 ≤ f.locals.size := by simpa [f] using hsize
  have hr : r.host.gas.Credits (54 * op + rest) := by
    simpa only [r, reserved, setGlobal] using paid_credits s op 5 (54 * op + rest)
      (hc.mono (show 5 * op + (54 * op + rest) ≤ 59 * cfg.regularOpCost + rest by dsimp [op]; omega))
  have linksR : Links r mi f.inst := links_setGlobal _ mi frame.inst globalIndex (.i32 (sp - 16)) (links_paid s mi frame.inst op 5 hlinks)
  have memoryR : r.mems[memoryIndex]? = some memory := by simpa only [r, reserved, setGlobal, paid, chargedStore] using hmem
  have globalR : r.globals[globalIndex]? = some {global with value := .i32 (sp - 16)} := by
    simp only [r, reserved, setGlobal, paid, chargedStore, Array.getElem?_modify, hglobal, Option.map_some, ite_true]
  have guardRule := wp_acquireGuardTail cfg fuel rest r limits base f callers code sp out cell mi globalIndex memoryIndex
    {global with value := .i32 (sp - 16)} memory post hout' hcell' hscratch hsize' linksR hgi globalR hmi memoryR hwf hcb hob
    haccept hnonzero hdepth hr
  have guardNext : WP cfg fuel (.next (atCode (acquireGuardTailStore r op globalIndex memoryIndex sp out cell memory)
      limits base.toArray (acquiredFrame f cell) callers code)) rest post := by
    simpa only [acquireStore, acquireGuardTailStore, acquireTailStore, r, f, acquireFrame, op] using hnext
  have guard := guardRule guardNext
  have blockRule := wp_block_empty cfg (fuel + 39) (54 * op + rest) r limits base.toArray f callers
    (WNear.Binary.InterfaceBorrow.acquireGuard ++ WNear.Binary.InterfaceBorrow.acquirePanic) tailCode post hr
  have blockNext : WP cfg (fuel + 39) (.next (atCode r limits base.toArray
      (emptyBlockFrame f base.toArray.size tailCode) callers
      (WNear.Binary.InterfaceBorrow.acquireGuard ++ WNear.Binary.InterfaceBorrow.acquirePanic))) (54 * op + rest) post := by
    simpa only [tailCode, List.size_toArray, op] using guard
  have block := blockRule blockNext
  have reserveRule := ValueReturnBorrow.wp_reserve cfg (fuel + 40) (54 * op + rest) s limits base.toArray frame callers
    (.block .empty (WNear.Binary.InterfaceBorrow.acquireGuard ++ WNear.Binary.InterfaceBorrow.acquirePanic) :: tailCode)
    mi globalIndex global sp 3 post hlinks.module hgi hglobal hsp (hc.mono (by dsimp [op]; omega))
  have reserveNext : WP cfg (fuel + 40) (.next (atCode (setGlobal (paid s op 5) globalIndex (.i32 (sp - 16))) limits base.toArray f callers
      (.block .empty (WNear.Binary.InterfaceBorrow.acquireGuard ++ WNear.Binary.InterfaceBorrow.acquirePanic) :: tailCode))) (54 * op + rest) post := by
    simpa only [r, reserved, Nat.add_assoc, Nat.reduceAdd] using block
  have result := reserveRule reserveNext
  rw [show 5 * cfg.regularOpCost + (54 * op + rest) = 59 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.InterfaceBorrow.acquireBody, WNear.Binary.ValueReturnAcquire.acquirePrologue,
    tailCode, List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

theorem acquireGuardTailStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out cell : UInt32) (memory : Memory) (hc : s.host.gas.Credits (54 * op + rest)) :
    (acquireGuardTailStore s op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 54 * op ∧
    (acquireGuardTailStore s op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
    (acquireGuardTailStore s op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
  have hg := guardStore_gas s op memoryIndex (12 * op + rest) cell memory (hc.mono (by omega))
  have ht := acquireTailStore_gas (guardStore s op memoryIndex cell memory) op globalIndex memoryIndex rest sp out cell
    (writeI32 memory cell.toNat 4294967295) hg.2.2
  refine ⟨?_, ht.2.1.trans hg.2.1, ht.2.2⟩
  change (acquireTailStore (guardStore s op memoryIndex cell memory) op globalIndex memoryIndex sp out cell _).host.gas.burnt = _
  rw [ht.1, hg.1]; omega

theorem acquireStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out cell : UInt32) (memory : Memory) (hc : s.host.gas.Credits (59 * op + rest)) :
    (acquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 59 * op ∧
    (acquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
    (acquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
  have hp := paid_gas s op 5 (54 * op + rest) (hc.mono (by omega))
  have cp : (reserved s op globalIndex sp).host.gas.Credits (54 * op + rest) := by
    simpa only [reserved, setGlobal] using paid_credits s op 5 (54 * op + rest) (hc.mono (show 5 * op + (54 * op + rest) ≤ 59 * op + rest by omega))
  have hg := acquireGuardTailStore_gas (reserved s op globalIndex sp) op globalIndex memoryIndex rest sp out cell memory cp
  have hburn : (reserved s op globalIndex sp).host.gas.burnt = s.host.gas.burnt + 5 * op := by simpa only [reserved, setGlobal] using hp.1
  have hpromises : (reserved s op globalIndex sp).host.gas.promises = s.host.gas.promises := by simpa only [reserved, setGlobal] using hp.2
  have result : (acquireGuardTailStore (reserved s op globalIndex sp) op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 59 * op ∧
      (acquireGuardTailStore (reserved s op globalIndex sp) op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
      (acquireGuardTailStore (reserved s op globalIndex sp) op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
    refine ⟨?_, hg.2.1.trans hpromises, hg.2.2⟩
    rw [hg.1, hburn]; omega
  simpa only [acquireStore, acquireGuardTailStore, acquireTailStore] using result

/-- Actual direct f441 acquisition, with nested f492/f672 and return included.
The panic location is ignored on this accepted path. -/
theorem wp_call_acquire (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp out cell location : UInt32) (mi : ModuleInst)
    (functionAddress globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory) (post : Post)
    (hlinks : Links s mi frame.inst)
    (hfi : mi.funcAddrs[441]? = some functionAddress)
    (hfn : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.ValueReturnAcquire.acquireSignature frame.inst WNear.Binary.InterfaceBorrow.acquireFunction))
    (hgi : mi.globalAddrs[0]? = some globalIndex) (hglobal : s.globals[globalIndex]? = some global)
    (hsp : global.value = .i32 sp) (hmi : mi.memAddrs[0]? = some memoryIndex)
    (hmem : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hcb : cell.toNat + 4 ≤ memory.byteSize) (hob : out.toNat + 8 ≤ memory.byteSize)
    (haccept : readI32 memory cell.toNat = 0) (hnonzero : cell ≠ 0)
    (hdepth : callers.length + 3 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (71 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledAcquireStore s cfg.regularOpCost globalIndex memoryIndex sp out cell memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 47) (.next (atCode s limits (base ++ [Value.i32 out, .i32 cell, .i32 location]).toArray
      frame callers (.call 441 :: code))) (71 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let callee : CallFrame :=
    {locals := #[.i32 out, .i32 cell, .i32 location, .i32 0, .i32 0]
     inst := frame.inst
     arity := 0
     height := base.length
     labels := []
     code := []}
  let saved := {frame with code}
  have hop := GasCounter.burn_credits s.host.gas op (70 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (59 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hl := links_charge _ mi frame.inst (11 * op) (links_charge s mi frame.inst op hlinks)
  have hmem' : (acquireEntryStore s op).mems[memoryIndex]? = some memory := by simpa only [acquireEntryStore, chargedStore] using hmem
  have hg' : (acquireEntryStore s op).globals[globalIndex]? = some global := by simpa only [acquireEntryStore, chargedStore] using hglobal
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
  have he := wp_call_wasm cfg (fuel + 46) (59 * op + rest) s limits base [.i32 out, .i32 cell, .i32 location]
    frame callers code 441 functionAddress mi WNear.Binary.ValueReturnAcquire.acquireSignature frame.inst
    WNear.Binary.InterfaceBorrow.acquireFunction post hlinks.module hfi hfn rfl (by omega)
  have hact : activationGas op (wasmLocals WNear.Binary.InterfaceBorrow.acquireFunction [.i32 out, .i32 cell, .i32 location]) = 11 * op := by
    simp [wasmLocals, WNear.Binary.InterfaceBorrow.acquireFunction, activationGas, ValType.default]
  rw [hact] at he
  have he' := he (hc.mono (by dsimp [op]; omega))
  have hbody'' : WP cfg (fuel + 46) (.next (wasmCallee (acquireEntryStore s op) limits base frame callers code
      WNear.Binary.ValueReturnAcquire.acquireSignature frame.inst WNear.Binary.InterfaceBorrow.acquireFunction
      [.i32 out, .i32 cell, .i32 location])) (59 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.ValueReturnAcquire.acquireSignature,
      WNear.Binary.InterfaceBorrow.acquireFunction, callee, saved, atCode, ValType.default, op] using hbody'
  have hall := he' hbody''
  rw [show fuel + 46 + 1 = fuel + 47 by omega,
    show cfg.regularOpCost + (11 * op + (59 * op + rest)) = 71 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  exact hall

theorem calledAcquireStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out cell : UInt32) (memory : Memory) (hc : s.host.gas.Credits (71 * op + rest)) :
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.burnt = s.host.gas.burnt + 71 * op ∧
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.promises = s.host.gas.promises ∧
    (calledAcquireStore s op globalIndex memoryIndex sp out cell memory).host.gas.Credits rest := by
  have hop := GasCounter.burn_credits s.host.gas op (70 * op + rest) (hc.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (59 * op + rest)
    (hop.2.2.2.mono (by omega))
  have hb := acquireStore_gas (acquireEntryStore s op) op globalIndex memoryIndex rest sp out cell memory ha.2.2.2
  refine ⟨?_, hb.2.1.trans (ha.2.2.1.trans hop.2.2.1), hb.2.2⟩
  change (acquireStore (acquireEntryStore s op) op globalIndex memoryIndex sp out cell memory).host.gas.burnt = _
  rw [hb.1]
  have he : (acquireEntryStore s op).host.gas.burnt = s.host.gas.burnt + op + 11 * op :=
    ha.2.1.trans (by rw [show (chargedStore s op).host.gas.burnt = s.host.gas.burnt + op from hop.2.1])
  rw [he]; omega


end WNear.Proofs.InterfaceBorrow
