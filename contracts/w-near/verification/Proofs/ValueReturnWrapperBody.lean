import Proofs.ValueReturnSlice
import Proofs.ValueReturnOuter
import Proofs.ValueReturnOuterState
import Proofs.ValueReturnOuterFinalState
import NearVM.MeteredWasmCall
import Proofs.ValueReturnDispatchGas
import Proofs.StorePairAddresses
import Proofs.TotalSupply

/-! Actual f545 slice wrapper. The prefix and epilogue below expose concrete
states for composition with the independently proved f456 body. -/
namespace WNear.Proofs.ValueReturnWrapperBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
open WNear.Proofs.ValueReturnWrapper (sliceStore sliceMemory)
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def reserved (s : Store NearState) (op index : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid s op 5) index (.i32 (sp - 16))
def preparedStore (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp pointer length : UInt32)
    (memory : Memory) : Store NearState :=
  paid (sliceStore (reserved s op globalIndex sp) op memoryIndex (sp - 16) pointer length memory) op 4
def preparedFrame (frame : CallFrame) (sp : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 2 (.i32 (sp - 16))}
def finalStore (afterCall : Store NearState) (op globalIndex : Nat) (sp : UInt32) : Store NearState :=
  setGlobal (paid afterCall op 4) globalIndex (.i32 sp)

/-- f545 has three live i32 locals at entry: its activation costs ten units. -/
theorem activation (op : Nat) (pointer length : UInt32) :
    activationGas op (wasmLocals WNear.Binary.ValueReturnWrapper.function [.i32 pointer, .i32 length]) = 10 * op := by
  simp [wasmLocals, WNear.Binary.ValueReturnWrapper.function, activationGas, ValType.default]

theorem sliceStore_resources (s : Store NearState) (op index : Nat) (scratch pointer length : UInt32) (memory : Memory) :
    {sliceStore s op index scratch pointer length memory with mems := s.mems, host := s.host} = s := by
  simp only [sliceStore, WNear.Proofs.ValueReturnWrapper.lengthStore, paid, chargedStore, storeI32]

theorem sliceStore_gas (s : Store NearState) (op index rest : Nat) (scratch pointer length : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (6 * op + rest)) :
    (sliceStore s op index scratch pointer length memory).host.gas.burnt = s.host.gas.burnt + 6 * op ∧
    (sliceStore s op index scratch pointer length memory).host.gas.promises = s.host.gas.promises ∧
    (sliceStore s op index scratch pointer length memory).host.gas.Credits rest := by
  let first := WNear.Proofs.ValueReturnWrapper.lengthStore s op index scratch length memory
  have h3 := paid_gas s op 3 (3 * op + rest) (hc.mono (by omega))
  have c3 : first.host.gas.Credits (3 * op + rest) := paid_credits s op 3 _ (hc.mono (by omega))
  have h6 := paid_gas first op 3 rest c3
  refine ⟨?_, h6.2.trans h3.2, paid_credits first op 3 rest c3⟩
  change (paid first op 3).host.gas.burnt = _
  rw [h6.1]
  change (paid s op 3).host.gas.burnt + 3 * op = _
  rw [h3.1]; omega

/-- Exact prefix effects and credits, before the real call456. -/
theorem preparedStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp pointer length : UInt32) (memory : Memory) (hc : s.host.gas.Credits (15 * op + rest)) :
    (preparedStore s op globalIndex memoryIndex sp pointer length memory).host.gas.burnt = s.host.gas.burnt + 15 * op ∧
    (preparedStore s op globalIndex memoryIndex sp pointer length memory).host.gas.promises = s.host.gas.promises ∧
    (preparedStore s op globalIndex memoryIndex sp pointer length memory).host.gas.Credits rest := by
  let r := reserved s op globalIndex sp
  let saved := sliceStore r op memoryIndex (sp - 16) pointer length memory
  have h5 := paid_gas s op 5 (10 * op + rest) (hc.mono (by omega))
  have c5 : r.host.gas.Credits (10 * op + rest) := paid_credits s op 5 _ (hc.mono (by omega))
  have h6 := sliceStore_gas r op memoryIndex (4 * op + rest) (sp - 16) pointer length memory (c5.mono (by omega))
  have h4 := paid_gas saved op 4 rest h6.2.2
  refine ⟨?_, h4.2.trans (h6.2.1.trans h5.2), paid_credits saved op 4 rest h6.2.2⟩
  change (paid saved op 4).host.gas.burnt = _
  rw [h4.1, h6.1]
  change (paid s op 5).host.gas.burnt + 6 * op + 4 * op = _
  rw [h5.1]; omega

theorem preparedStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp pointer length : UInt32) (memory : Memory) (hm : s.mems[memoryIndex]? = some memory) :
    (preparedStore s op globalIndex memoryIndex sp pointer length memory).mems[memoryIndex]? =
      some (sliceMemory memory (sp - 16) pointer length) := by
  have hr : (reserved s op globalIndex sp).mems[memoryIndex]? = some memory := by
    simpa only [reserved, setGlobal, paid, chargedStore] using hm
  have h := WNear.Proofs.ValueReturnWrapper.sliceStore_memory (reserved s op globalIndex sp) op memoryIndex
    (sp - 16) pointer length memory hr
  simpa only [preparedStore, paid, chargedStore] using h

theorem preparedStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp pointer length : UInt32) (memory : Memory) :
    (preparedStore s op globalIndex memoryIndex sp pointer length memory).globals =
      (setGlobal s globalIndex (.i32 (sp - 16))).globals := by
  have h := congrArg (fun t => t.globals) (sliceStore_resources (reserved s op globalIndex sp) op memoryIndex
    (sp - 16) pointer length memory)
  simpa only [preparedStore, reserved, paid, chargedStore, setGlobal] using h

theorem preparedStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp pointer length : UInt32) (memory : Memory) :
    {preparedStore s op globalIndex memoryIndex sp pointer length memory with
      mems := s.mems, globals := s.globals, host := s.host} = s := by
  simp only [preparedStore, reserved, sliceStore, WNear.Proofs.ValueReturnWrapper.lengthStore,
    paid, chargedStore, setGlobal, storeI32]

/-- The actual fifteen-opcode prefix saves the two words before constructing
f456's arguments. SP and all arithmetic use wrapping Wasm i32 semantics. -/
theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp pointer length : UInt32) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (global : GlobalInst) (memory : Memory) (post : Post)
    (hptr : frame.locals[0]? = some (.i32 pointer)) (hlen : frame.locals[1]? = some (.i32 length))
    (hsize : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hgi : mi.globalAddrs[0]? = some globalIndex)
    (hg : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmi : mi.memAddrs[0]? = some memoryIndex) (hmem : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hspan : (sp - 16).toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (preparedStore s cfg.regularOpCost globalIndex memoryIndex sp pointer length memory)
      limits ((stack.push (.i32 1055020)).push (.i32 (sp - 16 + 8))) (preparedFrame frame sp) callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits stack frame callers
      ((WNear.Binary.ValueReturnWrapper.prologue ++ WNear.Binary.ValueReturnWrapper.saveSlice ++
        WNear.Binary.ValueReturnWrapper.arguments) ++ code))) (15 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let r := reserved s op globalIndex sp
  let saved := sliceStore r op memoryIndex (sp - 16) pointer length memory
  let frame' := preparedFrame frame sp
  have hscratch : frame'.locals[2]? = some (.i32 (sp - 16)) := by
    simp [frame', preparedFrame, show 2 < frame.locals.size by omega]
  have hptr' : frame'.locals[0]? = some (.i32 pointer) := by simpa [frame', preparedFrame] using hptr
  have hlen' : frame'.locals[1]? = some (.i32 length) := by simpa [frame', preparedFrame] using hlen
  have cr : r.host.gas.Credits (10 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have cs : saved.host.gas.Credits (4 * op + rest) := WNear.Proofs.ValueReturnWrapper.sliceStore_credits r op memoryIndex
    (sp - 16) pointer length memory _ (cr.mono (by omega))
  have hargs := WNear.Proofs.ValueReturnWrapper.wp_arguments cfg fuel rest saved limits stack frame' callers code (sp - 16)
    post hscratch cs
  have hargs' := hargs hnext
  have hmR : r.modules[frame'.inst]? = some mi := by
    simpa only [r, reserved, setGlobal, paid, chargedStore, frame', preparedFrame] using hm
  have hmemR : r.mems[memoryIndex]? = some memory := by simpa only [r, reserved, setGlobal, paid, chargedStore] using hmem
  have hsave := WNear.Proofs.ValueReturnWrapper.wp_save_slice cfg (fuel + 4) (4 * op + rest) r limits stack frame' callers
    (WNear.Binary.ValueReturnWrapper.arguments ++ code) (sp - 16) pointer length mi memoryIndex memory post
    hscratch hptr' hlen' hmR hmi hmemR hwf hspan (cr.mono (by omega))
  have hsave' := hsave hargs'
  rw [show fuel + 4 + 6 = fuel + 10 by omega,
    show 6 * cfg.regularOpCost + (4 * op + rest) = 10 * op + rest by dsimp [op]; omega] at hsave'
  have hreserve := WNear.Proofs.ValueReturnBorrow.wp_reserve cfg (fuel + 10) (10 * op + rest) s limits stack frame callers
    (WNear.Binary.ValueReturnWrapper.saveSlice ++ WNear.Binary.ValueReturnWrapper.arguments ++ code)
    mi globalIndex global sp 2 post hm hgi hg hsp (hc.mono (by dsimp [op]; omega))
  have hsave'' : WP cfg (fuel + 10) (.next (atCode r limits stack frame' callers
      (WNear.Binary.ValueReturnWrapper.saveSlice ++ WNear.Binary.ValueReturnWrapper.arguments ++ code)))
      (10 * op + rest) post := by simpa only [List.append_assoc] using hsave'
  have hall := hreserve hsave''
  rw [show fuel + 10 + 5 = fuel + 15 by omega,
    show 5 * cfg.regularOpCost + (10 * op + rest) = 15 * cfg.regularOpCost + rest by dsimp [op]; omega] at hall
  simpa only [WNear.Binary.ValueReturnWrapper.prologue, List.append_assoc] using hall

/-- The final four actual wrapper instructions restore the saved SP. -/
theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sp : UInt32) (mi : ModuleInst) (globalIndex : Nat) (global : GlobalInst) (post : Post)
    (hscratch : frame.locals[2]? = some (.i32 (sp - 16)))
    (hm : s.modules[frame.inst]? = some mi) (hgi : mi.globalAddrs[0]? = some globalIndex)
    (hg : s.globals[globalIndex]? = some global)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore s cfg.regularOpCost globalIndex sp) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers (WNear.Binary.ValueReturnWrapper.epilogue ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  have h := WNear.Proofs.ValueReturnBorrow.wp_restore cfg fuel rest s limits stack frame callers code mi globalIndex
    global (sp - 16) 2 post hscratch hm hgi hg hc
  apply h
  simpa only [finalStore, UInt32.sub_add_cancel] using hnext

theorem preparedStore_cost (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp pointer length : UInt32) (memory : Memory) (returnLength : Nat) :
    ValueReturnHost.cost (preparedStore s op globalIndex memoryIndex sp pointer length memory).host returnLength =
      ValueReturnHost.cost s.host returnLength := by
  rw [preparedStore, ValueReturnDispatchGas.cost_paid]
  change ValueReturnHost.cost (paid (WNear.Proofs.ValueReturnWrapper.lengthStore (reserved s op globalIndex sp)
    op memoryIndex (sp - 16) length memory) op 3).host returnLength = _
  rw [ValueReturnDispatchGas.cost_paid]
  change ValueReturnHost.cost (paid (reserved s op globalIndex sp) op 3).host returnLength = _
  rw [ValueReturnDispatchGas.cost_paid]
  change ValueReturnHost.cost (paid s op 5).host returnLength = _
  exact ValueReturnDispatchGas.cost_paid s op 5 returnLength

/-- The saved slice passed to456 contains exactly the original two i32 values
zero-extended to i64 by its real load32_u instructions. -/
theorem preparedMemory_readback (memory : Memory) (sp pointer length : UInt32)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hspan : (sp - 16).toNat + 16 ≤ memory.byteSize) :
    ValueReturnDispatch.packed32 (sliceMemory memory (sp - 16) pointer length) (sp - 16 + 8).toNat =
      UInt64.ofNat pointer.toNat ∧
    ValueReturnDispatch.packed32 (sliceMemory memory (sp - 16) pointer length) ((sp - 16 + 8).toNat + 4) =
      UInt64.ofNat length.toNat := by
  have hs := ValueReturnSlice.sliceMemory_spec memory (sp - 16) pointer length hwf hspan
  have ha := WNear.Proofs.StorePairAddresses.add_eight_memory memory (sp - 16) hwidth hspan
  rw [ha]
  exact ⟨hs.2.2.2.1, by simpa only [Nat.add_assoc, Nat.reduceAdd] using hs.2.2.2.2.1⟩

theorem finalStore_gas (s : Store NearState) (op globalIndex rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (4 * op + rest)) :
    (finalStore s op globalIndex sp).host.gas.burnt = s.host.gas.burnt + 4 * op ∧
    (finalStore s op globalIndex sp).host.gas.promises = s.host.gas.promises ∧
    (finalStore s op globalIndex sp).host.gas.Credits rest :=
  ⟨(paid_gas s op 4 rest hc).1, (paid_gas s op 4 rest hc).2, paid_credits s op 4 rest hc⟩

theorem finalStore_resources (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) :
    {finalStore s op globalIndex sp with globals := s.globals, host := s.host} = s := by
  simp only [finalStore, setGlobal, paid, chargedStore]

/-- The wrapper's scalar prefix does not change any functional host field. -/
theorem preparedStore_host (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp pointer length : UInt32) (memory : Memory) :
    {(preparedStore s op globalIndex memoryIndex sp pointer length memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [preparedStore, reserved, sliceStore, WNear.Proofs.ValueReturnWrapper.lengthStore,
    paid, chargedStore, setGlobal, storeI32, chargeHost]

/-- Restoring the guest SP after value_return retains the exact returned bytes,
promise selection, logs, storage, context and every other functional host field. -/
theorem finalStore_host (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) :
    {(finalStore s op globalIndex sp).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [finalStore, setGlobal, paid, chargedStore, chargeHost]

theorem finalStore_returnData (s : Store NearState) (op globalIndex : Nat) (sp : UInt32) :
    (finalStore s op globalIndex sp).host.returnData = s.host.returnData ∧
    (finalStore s op globalIndex sp).host.returnedPromise = s.host.returnedPromise := by
  have h := finalStore_host s op globalIndex sp
  exact ⟨congrArg (fun host => host.returnData) h, congrArg (fun host => host.returnedPromise) h⟩

/-- The concrete post-dispatch cleanup, including the counter decrement and
zero-status check, has no functional host effect. -/
theorem cleanupAfter_host (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (scratch counter : UInt32) (memory : Memory) :
    {(ValueReturnOuter.cleanupAfter s op globalIndex memoryIndex scratch counter memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [ValueReturnOuter.cleanupAfter, ValueReturnOuter.epilogueAfter,
    ValueReturnOuter.checkAfter, ValueReturnOuter.releaseAfter, ValueReturnOuter.nonnullEntry,
    ValueReturnBorrow.checkedStore, ValueReturnBorrowCounters.releasedStore,
    ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapEntryStore,
    ValueReturnBorrowCounters.swapStore, paid, chargedStore, setGlobal, storeI32, chargeHost]

/-- Completing both concrete cleanup layers retains the value_return payload.
The only premises resolve the actual memory of the terminal host call. -/
theorem suffix_returnData (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex globalIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (scratch counter wrapperSp : UInt32)
    (hi : mi.memAddrs[0]? = some memoryIndex) (hm : s.mems[memoryIndex]? = some memory) :
    (finalStore (ValueReturnOuter.cleanupAfter (ValueReturnDispatch.fragmentAfter cfg s mi len ptr)
      cfg.regularOpCost globalIndex memoryIndex scratch counter memory) cfg.regularOpCost globalIndex wrapperSp).host.returnData =
      some (memory.readList ptr.toNat len.toNat) ∧
    (finalStore (ValueReturnOuter.cleanupAfter (ValueReturnDispatch.fragmentAfter cfg s mi len ptr)
      cfg.regularOpCost globalIndex memoryIndex scratch counter memory) cfg.regularOpCost globalIndex wrapperSp).host.returnedPromise = none := by
  have hf := ValueReturnDispatchGas.fragmentAfter_returnData cfg s mi memoryIndex memory len ptr hi hm
  have hc := cleanupAfter_host (ValueReturnDispatch.fragmentAfter cfg s mi len ptr) cfg.regularOpCost globalIndex
    memoryIndex scratch counter memory
  have hd := finalStore_returnData (ValueReturnOuter.cleanupAfter (ValueReturnDispatch.fragmentAfter cfg s mi len ptr)
    cfg.regularOpCost globalIndex memoryIndex scratch counter memory) cfg.regularOpCost globalIndex wrapperSp
  exact ⟨hd.1.trans ((congrArg (fun host => host.returnData) hc).trans hf.1),
    hd.2.trans ((congrArg (fun host => host.returnedPromise) hc).trans hf.2)⟩

theorem hostAfter_storage (st : HostStore NearState) (len ptr : UInt64) :
    (ValueReturnHost.after st len ptr).host.storage = st.host.storage := by
  have h := Wasm.Near.MeteredHosts.applyCharges_frame st.host (ValueReturnHost.plan st.host len.toNat)
    (by simp [ValueReturnHost.plan, Wasm.Near.MeteredHosts.BurnsOnly])
  have hs := congrArg (fun host => host.storage) h
  simpa only [ValueReturnHost.after, Wasm.Near.MeteredHosts.Output.paidStore] using hs

/-- Actual terminal dispatch changes no persistent storage. -/
theorem fragment_storage (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (len ptr : UInt64) :
    (ValueReturnDispatch.fragmentAfter cfg s mi len ptr).host.storage = s.host.storage := by
  let before := ValueReturnHost.beforeCall cfg
    (paid (ValueReturnDispatch.calleeStore cfg (paid s cfg.regularOpCost 9)) cfg.regularOpCost 2) mi
  have h := hostAfter_storage before len ptr
  simpa only [ValueReturnDispatch.fragmentAfter, ValueReturnDispatch.after, ValueReturnLeaf.finalStore,
    ValueReturnHost.callStore, commitHost_host, before, ValueReturnHost.beforeCall,
    ValueReturnDispatch.calleeStore, paid, chargedStore, chargeHost] using h

/-- Both concrete cleanup layers preserve the pre-dispatch persistent storage. -/
theorem suffix_storage (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex globalIndex : Nat) (memory : Memory) (len ptr : UInt64) (scratch counter wrapperSp : UInt32) :
    (finalStore (ValueReturnOuter.cleanupAfter (ValueReturnDispatch.fragmentAfter cfg s mi len ptr)
      cfg.regularOpCost globalIndex memoryIndex scratch counter memory) cfg.regularOpCost globalIndex wrapperSp).host.storage = s.host.storage := by
  have hf := fragment_storage cfg s mi len ptr
  have hc := cleanupAfter_host (ValueReturnDispatch.fragmentAfter cfg s mi len ptr) cfg.regularOpCost globalIndex
    memoryIndex scratch counter memory
  have hd := finalStore_host (ValueReturnOuter.cleanupAfter (ValueReturnDispatch.fragmentAfter cfg s mi len ptr)
    cfg.regularOpCost globalIndex memoryIndex scratch counter memory) cfg.regularOpCost globalIndex wrapperSp
  exact (congrArg (fun host => host.storage) hd).trans ((congrArg (fun host => host.storage) hc).trans hf)

/-- Actual state at456 entry after its caller opcode and ten-unit activation. -/
def outerEntry (s : Store NearState) (op globalIndex memoryIndex : Nat) (sp pointer length : UInt32)
    (memory : Memory) : Store NearState :=
  chargedStore (chargedStore (preparedStore s op globalIndex memoryIndex sp pointer length memory) op) (10 * op)

def outerLeaf (frame : CallFrame) (base : List Value) (sp : UInt32) : CallFrame :=
  {locals := #[.i32 1055020, .i32 (sp - 16 + 8), .i32 0, .i32 0]
   inst := frame.inst
   arity := 0
   height := base.length
   labels := []
   code := []}

def afterOuter (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (memory : Memory) (p : ValueReturnOuterBody.Layout) : Store NearState :=
  ValueReturnOuterBody.finalStore cfg (outerEntry s cfg.regularOpCost globalIndex memoryIndex sp pointer length memory) p

def completeStore (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (memory : Memory) (p : ValueReturnOuterBody.Layout) : Store NearState :=
  finalStore (afterOuter cfg s sp pointer length globalIndex memoryIndex memory p) cfg.regularOpCost globalIndex sp

/-- Ready is a record of code, heap reads, bounds and limits. Altering the
saved caller's continuation does not change any of these primitive facts. -/
theorem outerReady_continuation (cfg : WasmConfig) (extra : Nat) (s : Store NearState)
    (limits : ExecLimits) (leaf saved saved' : CallFrame) (callers : List CallFrame)
    (p : ValueReturnOuterBody.Layout)
    (hr : ValueReturnOuterBody.Ready cfg extra s limits leaf (saved :: callers) p) :
    ValueReturnOuterBody.Ready cfg extra s limits leaf (saved' :: callers) p := by
  exact {hr with depth := hr.depth}

def fee (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (memory : Memory) (p : ValueReturnOuterBody.Layout) : Nat :=
  ValueReturnHost.cost (ValueReturnOuterBody.dispatchBefore
    (outerEntry s cfg.regularOpCost globalIndex memoryIndex sp pointer length memory) cfg.regularOpCost p).host p.len.toNat

def bodyBudget (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (memory : Memory) (p : ValueReturnOuterBody.Layout) : Nat :=
  267 * cfg.regularOpCost + fee cfg s sp pointer length globalIndex memoryIndex memory p

/-- Paying the exact scalar prefix and456 activation leaves its full body
budget, plus the actual four-opcode545 epilogue and the caller's reserve. -/
theorem outerEntry_credits (cfg : WasmConfig) (s : Store NearState) (rest : Nat) (sp pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (memory : Memory) (p : ValueReturnOuterBody.Layout)
    (hc : s.host.gas.Credits (bodyBudget cfg s sp pointer length globalIndex memoryIndex memory p + rest)) :
    (outerEntry s cfg.regularOpCost globalIndex memoryIndex sp pointer length memory).host.gas.Credits
      (237 * cfg.regularOpCost + fee cfg s sp pointer length globalIndex memoryIndex memory p +
        (4 * cfg.regularOpCost + rest)) := by
  let op := cfg.regularOpCost
  let f := fee cfg s sp pointer length globalIndex memoryIndex memory p
  let prepared := preparedStore s op globalIndex memoryIndex sp pointer length memory
  have cp := (preparedStore_gas s op globalIndex memoryIndex (252 * op + f + rest) sp pointer length memory
    (hc.mono (by dsimp [bodyBudget, op, f]; omega))).2.2
  have hop := GasCounter.burn_credits prepared.host.gas op (251 * op + f + rest) (cp.mono (by omega))
  have ha := GasCounter.burn_credits (chargedStore prepared op).host.gas (10 * op)
    (237 * op + f + (4 * op + rest)) (hop.2.2.2.mono (by omega))
  exact ha.2.2.2

/-- Only the depth bound of primitive Ready depends on the saved callers. -/
theorem outerReady_callers (cfg : WasmConfig) (extra : Nat) (s : Store NearState)
    (limits : ExecLimits) (leaf : CallFrame) (callers callers' : List CallFrame)
    (p : ValueReturnOuterBody.Layout) (hlen : callers'.length = callers.length)
    (hr : ValueReturnOuterBody.Ready cfg extra s limits leaf callers p) :
    ValueReturnOuterBody.Ready cfg extra s limits leaf callers' p := by
  exact {hr with depth := by rw [hlen]; exact hr.depth}

def entered545 (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (10 * op)
def leaf545 (inst : Nat) (pointer length : UInt32) : CallFrame :=
  WNear.Proofs.StorePair.voidFrame #[.i32 pointer, .i32 length, .i32 0] inst
def calledStore (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (memory : Memory) (p : ValueReturnOuterBody.Layout) : Store NearState :=
  completeStore cfg (entered545 s cfg.regularOpCost) sp pointer length p.globalIndex p.memoryIndex memory p

def callFee (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (memory : Memory) (p : ValueReturnOuterBody.Layout) : Nat :=
  fee cfg (entered545 s cfg.regularOpCost) sp pointer length p.globalIndex p.memoryIndex memory p

/-- A single structural resource record for the actual returning545 call.
Every field is a loader lookup, memory predicate or primitive Ready fact on
an explicitly computed phase. No guest execution result is assumed. -/
structure Resources (cfg : WasmConfig) (extra : Nat) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (sp pointer length : UInt32) (memory : Memory) (p : ValueReturnOuterBody.Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  functionIndex : p.mi.funcAddrs[545]? = some 545
  function : s.funcs[545]? = some (.wasm WNear.Binary.ValueReturnWrapper.signature frame.inst WNear.Binary.ValueReturnWrapper.function)
  outerIndex : p.mi.funcAddrs[456]? = some 456
  outerFunction : s.funcs[456]? = some (.wasm WNear.Binary.ValueReturnOuter.signature frame.inst WNear.Binary.ValueReturnOuter.function)
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some {p.global with value := .i32 sp}
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memoryLookup : s.mems[p.memoryIndex]? = some memory
  memoryWf : memory.wf
  scratchBound : (sp - 16).toNat + 16 ≤ memory.byteSize
  outerSp : p.sp = sp - 16
  outerInterface : p.interface = 1055020
  outerSlice : p.slice = sp - 16 + 8
  outerMemory : p.memory = sliceMemory memory (sp - 16) pointer length
  outer : ValueReturnOuterBody.Ready cfg extra
    (outerEntry (entered545 s cfg.regularOpCost) cfg.regularOpCost p.globalIndex p.memoryIndex sp pointer length memory)
    limits (outerLeaf (leaf545 frame.inst pointer length) [] sp)
    [preparedFrame (leaf545 frame.inst pointer length) sp, frame] p

/-- All computation before the terminal host call is internal Wasm work.
Its receipt-byte pricing uses the original guest-visible fee context. -/
theorem fee_eq (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (globalIndex memoryIndex : Nat) (memory : Memory) (p : ValueReturnOuterBody.Layout) :
    fee cfg s sp pointer length globalIndex memoryIndex memory p = ValueReturnHost.cost s.host p.len.toNat := by
  simp only [fee, outerEntry, preparedStore, reserved, sliceStore, WNear.Proofs.ValueReturnWrapper.lengthStore,
    ValueReturnOuterBody.dispatchBefore, ValueReturnOuterBody.status, ValueReturnOuterBody.low,
    ValueReturnOuterBody.high, ValueReturnOuterBody.acquired, ValueReturnOuterBody.arguments,
    ValueReturnOuterBody.looked, ValueReturnOuterBody.lookupBefore, ValueReturnOuterBody.reserved,
    ValueReturnOuter.nonnullAfter, ValueReturnOuter.nonnullEntry,
    ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.indirectEntered,
    ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered,
    ValueReturnAcquire.calledAcquireStore, ValueReturnAcquire.acquireStore, ValueReturnAcquire.acquireEntryStore,
    ValueReturnAcquire.reserved, ValueReturnAcquire.recordStore, ValueReturnAcquire.guardStore,
    ValueReturnAcquire.calledIncrementStore, ValueReturnAcquire.incrementStore, ValueReturnAcquire.incrementEntryStore,
    ValueReturnBorrowCounters.calledSwapStore, ValueReturnBorrowCounters.swapStore, ValueReturnBorrowCounters.swapEntryStore,
    ValueReturnHost.cost, ValueReturnHost.dataCost, paid, chargedStore, setGlobal, storeI32, chargeHost]

theorem callFee_eq (cfg : WasmConfig) (s : Store NearState) (sp pointer length : UInt32)
    (memory : Memory) (p : ValueReturnOuterBody.Layout) :
    callFee cfg s sp pointer length memory p = ValueReturnHost.cost s.host p.len.toNat := by
  rw [callFee, fee_eq]
  rfl

/-- Actual456 phase framing discharges the epilogue's code lookup. -/
theorem Resources.afterModule (cfg : WasmConfig) (extra : Nat) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (sp pointer length : UInt32) (memory : Memory) (p : ValueReturnOuterBody.Layout)
    (hr : Resources cfg extra s limits frame sp pointer length memory p) :
    (afterOuter cfg (entered545 s cfg.regularOpCost) sp pointer length p.globalIndex p.memoryIndex memory p).modules[frame.inst]? = some p.mi := by
  have h := (ValueReturnOuterBody.finalStore_code cfg
    (outerEntry (entered545 s cfg.regularOpCost) cfg.regularOpCost p.globalIndex p.memoryIndex sp pointer length memory)
    p frame.inst extra hr.outer.code).module
  simpa only [afterOuter] using h

/-- Actual456 cleanup restores its incoming global; no post-state lookup is
part of Resources. -/
theorem Resources.afterGlobal (cfg : WasmConfig) (extra : Nat) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (sp pointer length : UInt32) (memory : Memory) (p : ValueReturnOuterBody.Layout)
    (hr : Resources cfg extra s limits frame sp pointer length memory p) :
    (afterOuter cfg (entered545 s cfg.regularOpCost) sp pointer length p.globalIndex p.memoryIndex memory p).globals[p.globalIndex]? = some p.global := by
  have h := ValueReturnOuterBody.finalStore_global cfg
    (outerEntry (entered545 s cfg.regularOpCost) cfg.regularOpCost p.globalIndex p.memoryIndex sp pointer length memory)
    p hr.outer.global hr.outer.sp
  simpa only [afterOuter] using h

end WNear.Proofs.ValueReturnWrapperBody
