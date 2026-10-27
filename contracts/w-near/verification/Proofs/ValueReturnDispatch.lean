import Proofs.ValueReturnLeaf
import NearVM.MeteredIndirectCall
import NearVM.MeteredI32MemoryRules
import Binary.ValueReturnDispatch

/-! Concrete indirect trait dispatch to deployed f260 and its actual host call.
Thread-local/RefCell acquisition before this dispatch remains separate. -/
namespace WNear.Proofs.ValueReturnDispatch
open Wasm Wasm.Near MeteredLogic
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

/-- An indirect-call opcode is followed by the actual eleven-unit activation. -/
def calleeStore (cfg : WasmConfig) (s : Store NearState) : Store NearState :=
  chargedStore (chargedStore s cfg.regularOpCost) (11 * cfg.regularOpCost)

def after (cfg : WasmConfig) (s : Store NearState) (calleeModule : ModuleInst)
    (len ptr : UInt64) : Store NearState :=
  ValueReturnLeaf.finalStore cfg (calleeStore cfg s) calleeModule len ptr

/-- The actual type-four/table-zero dispatch, returning to the unchanged caller
suffix. Every premise is a primitive lookup, span/limit fact, or gas resource. -/
theorem wp_indirect (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (receiver : UInt32) (len ptr : UInt64) (element : UInt32)
    (callerModule calleeModule : ModuleInst) (tableAddress functionAddress inst hostAddress memoryIndex : Nat)
    (table : TableInst) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some callerModule)
    (htableAddress : callerModule.tableAddrs[0]? = some tableAddress)
    (htable : s.tables[tableAddress]? = some table)
    (helement : table.elems[element.toNat]? = some (.func functionAddress))
    (htype : callerModule.types[4]? = some WNear.Binary.ValueReturnLeaf.signature)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function))
    (hcalleeModule : s.modules[inst]? = some calleeModule)
    (hhostAddress : calleeModule.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : calleeModule.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s calleeModule len ptr) limits base.toArray
      frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits
      ((base ++ [Value.i32 receiver, Value.i64 len, Value.i64 ptr]).toArray.push (.i32 element))
      frame callers (.call_indirect 4 0 :: code)))
      (15 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) post := by
  let op := cfg.regularOpCost
  let remaining := 3 * op + ValueReturnHost.cost s.host len.toNat + rest
  let localValues : Array Value := #[.i32 receiver, .i64 len, .i64 ptr]
  let calleeFrame : CallFrame :=
    {locals := localValues, inst, arity := 0, height := base.length, labels := [], code := []}
  let saved : CallFrame := {frame with code}
  have h0 : s.host.gas.Credits (op + (11 * op + remaining)) := hc.mono (by dsimp [op, remaining]; omega)
  have hop := GasCounter.burn_credits s.host.gas op (11 * op + remaining) h0
  have hactivation := GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) remaining hop.2.2.2
  have hcalleeCredits : (calleeStore cfg s).host.gas.Credits
      (3 * op + ValueReturnHost.cost (calleeStore cfg s).host len.toNat + rest) := hactivation.2.2.2
  have hcm : (calleeStore cfg s).modules[inst]? = some calleeModule := by
    simpa only [calleeStore, chargedStore] using hcalleeModule
  have hh : (calleeStore cfg s).funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn) := by
    simpa only [calleeStore, chargedStore] using hhost
  have hmem : (calleeStore cfg s).mems[memoryIndex]? = some memory := by
    simpa only [calleeStore, chargedStore] using hmemory
  have hg := (ValueReturnLeaf.finalStore_gas cfg extra rest (calleeStore cfg s) calleeModule
    memoryIndex memory len ptr hmemoryIndex hmem hfixed hbound hlimit hcalleeCredits).2.2
  have hleave := wp_leave_wasm cfg fuel rest (after cfg s calleeModule len ptr) limits base []
    calleeFrame saved callers post rfl rfl rfl hg
  simp only [List.append_nil] at hleave
  have hleave' : WP cfg (fuel + 1) (.next (atCode (after cfg s calleeModule len ptr) limits
      base.toArray calleeFrame (saved :: callers) [])) rest post := by
    apply hleave
    simpa only [saved, atCode, List.append_nil] using hnext
  have hbody := ValueReturnLeaf.wp_body cfg extra (fuel + 1) rest (calleeStore cfg s) limits base
    calleeFrame (saved :: callers) [] len ptr calleeModule hostAddress memoryIndex memory post
    rfl rfl hcm hhostAddress hh hmemoryIndex hmem hfixed hbound hlimit hcalleeCredits hleave'
  have hact : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.ValueReturnLeaf.function [.i32 receiver, .i64 len, .i64 ptr]) = 11 * op := by
    simpa [wasmLocals, WNear.Binary.ValueReturnLeaf.function, op] using
      WNear.Binary.ValueReturnLeaf.activation_cost cfg.regularOpCost receiver len ptr
  have hentry := wp_call_indirect_wasm cfg (fuel + 4) remaining s limits base
    [.i32 receiver, .i64 len, .i64 ptr] frame callers code 4 0 tableAddress functionAddress element table
    callerModule WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function post
    hmodule htableAddress htable helement htype hfunction rfl hdepth
  rw [hact] at hentry
  have hbody' : WP cfg (fuel + 4)
      (.next (wasmCallee (calleeStore cfg s) limits base frame callers code
        WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function
        [.i32 receiver, .i64 len, .i64 ptr])) remaining post := by
    convert hbody using 1 <;> first | omega | rfl
  have hall := hentry h0 hbody'
  dsimp only [remaining, op] at hall
  convert hall using 1
  omega

/-- Zero-extension of the actual four-byte little-endian memory read. -/
def packed32 (memory : Memory) (address : Nat) : UInt64 :=
  UInt64.ofNat ((List.range 4).foldr
    (fun i acc => acc * 256 + (memory.read8 (address + i)).toNat) 0)

/-- Actual i64.load32_u, without a load-success callback. -/
theorem wp_load32_u (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg) (address : UInt32)
    (mi : ModuleInst) (memoryIndex : Nat) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hbound : address.toNat + arg.offset + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore s cfg.regularOpCost) limits
      (stack.push (.i64 (packed32 memory (address.toNat + arg.offset)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode s limits (stack.push (.i32 address)) frame callers
      (.load .i64 (some {bits := 32, signed := false}) arg :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode s limits (stack.push (.i32 address)) frame callers
    (.load .i64 (some {bits := 32, signed := false}) arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore s cfg.regularOpCost) limits
        (stack.push (.i64 (packed32 memory (address.toNat + arg.offset)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore,
      Exec.loadNat, Store.memOf, getElem!_def, hmodule, hmemoryIndex, hmemory,
      Memory.readNat, Memory.inBounds, hbound, packed32]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- The successful RefCell pointer from f430 is retained in local three. -/
def dispatchFrame (frame : CallFrame) (cell : UInt32) : CallFrame :=
  {frame with locals := frame.locals.set! 3 (.i32 cell)}

/-- The nine actual scalar operations before f456's indirect call. All values
are derived from primitive memory reads; aliases require no separation premise. -/
theorem wp_prepare (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell slice receiver vtable element : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (memoryIndex : Nat) (memory : Memory) (post : Post)
    (hslice : frame.locals[1]? = some (.i32 slice)) (hsize : 4 ≤ frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some mi) (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hcell : cell.toNat + 8 ≤ memory.byteSize) (hspan : slice.toNat + 8 ≤ memory.byteSize)
    (hvtable : vtable.toNat + 96 ≤ memory.byteSize)
    (hreceiverRead : readI32 memory cell.toNat = receiver)
    (hvtableRead : readI32 memory (cell.toNat + 4) = vtable)
    (helementRead : readI32 memory (vtable.toNat + 92) = element)
    (hlenRead : packed32 memory (slice.toNat + 4) = len)
    (hptrRead : packed32 memory slice.toNat = ptr)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (StorePairCaller.paid s cfg.regularOpCost 9) limits
      ((base ++ [Value.i32 receiver, Value.i64 len, Value.i64 ptr]).toArray.push (.i32 element))
      (dispatchFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers
      ([.local_tee 3, .load .i32 none {align := 2, offset := 0},
        .local_get 1, .load .i64 (some {bits := 32, signed := false}) {align := 2, offset := 4},
        .local_get 1, .load .i64 (some {bits := 32, signed := false}) {align := 2, offset := 0},
        .local_get 3, .load .i32 none {align := 2, offset := 4},
        .load .i32 none {align := 2, offset := 92}] ++ code)))
      (9 * cfg.regularOpCost + rest) post := by
  let frame' := dispatchFrame frame cell
  have hs : frame'.locals[1]? = some (.i32 slice) := by simpa [frame', dispatchFrame] using hslice
  have hcellLocal : frame'.locals[3]? = some (.i32 cell) := by
    simp [frame', dispatchFrame, show 3 < frame.locals.size by omega]
  have hm (n : Nat) : (StorePairCaller.paid s cfg.regularOpCost n).modules[frame'.inst]? = some mi := by
    have he := StorePairCaller.paid_resources s cfg.regularOpCost n
    have hf := congrArg (fun store : Store NearState => store.modules[frame.inst]?) he
    simpa only [frame', dispatchFrame] using hf.trans hmodule
  have hmem (n : Nat) : (StorePairCaller.paid s cfg.regularOpCost n).mems[memoryIndex]? = some memory := by
    have he := StorePairCaller.paid_resources s cfg.regularOpCost n
    have hf := congrArg (fun store : Store NearState => store.mems[memoryIndex]?) he
    exact hf.trans hmemory
  rw [show 9 * cfg.regularOpCost + rest = cfg.regularOpCost + (8 * cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 8) (8 * cfg.regularOpCost + rest) s limits base.toArray frame callers _ 3 (.i32 cell) post (hc.mono (by omega))
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 7) (7 * cfg.regularOpCost + rest) (StorePairCaller.paid s cfg.regularOpCost 1)
    limits base.toArray frame' callers _ {align := 2, offset := 0} cell mi memoryIndex memory post
    (hm 1) hmemoryIndex (hmem 1) (by change cell.toNat + 0 + 4 ≤ memory.byteSize; omega)
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  simp only [Nat.add_zero, hreceiverRead]
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) (6 * cfg.regularOpCost + rest) _ limits _ frame' callers _ 1 (.i32 slice) post hs
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_load32_u cfg (fuel + 5) (5 * cfg.regularOpCost + rest) (StorePairCaller.paid s cfg.regularOpCost 3)
    limits _ frame' callers _ {align := 2, offset := 4} slice mi memoryIndex memory post
    (hm 3) hmemoryIndex (hmem 3) (by change slice.toNat + 4 + 4 ≤ memory.byteSize; omega)
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [hlenRead]
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) _ limits _ frame' callers _ 1 (.i32 slice) post hs
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_load32_u cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (StorePairCaller.paid s cfg.regularOpCost 5)
    limits _ frame' callers _ {align := 2, offset := 0} slice mi memoryIndex memory post
    (hm 5) hmemoryIndex (hmem 5) (by change slice.toNat + 0 + 4 ≤ memory.byteSize; omega)
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  simp only [Nat.add_zero, hptrRead]
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) _ limits _ frame' callers _ 3 (.i32 cell) post hcellLocal
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) (cfg.regularOpCost + rest) (StorePairCaller.paid s cfg.regularOpCost 7)
    limits _ frame' callers _ {align := 2, offset := 4} cell mi memoryIndex memory post
    (hm 7) hmemoryIndex (hmem 7) (by change cell.toNat + 4 + 4 ≤ memory.byteSize; omega)
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  rw [hvtableRead]
  apply wp_i32_load cfg fuel rest (StorePairCaller.paid s cfg.regularOpCost 8)
    limits _ frame' callers code {align := 2, offset := 92} vtable mi memoryIndex memory post
    (hm 8) hmemoryIndex (hmem 8) (by change vtable.toNat + 92 + 4 ≤ memory.byteSize; omega)
  · exact StorePairCaller.paid_credits s cfg.regularOpCost 8 _ (hc.mono (by omega))
  · simpa [StorePairCaller.paid, helementRead] using hnext

/-- Store after the actual f456 fragment, including the terminal host return. -/
def fragmentAfter (cfg : WasmConfig) (s : Store NearState) (calleeModule : ModuleInst)
    (len ptr : UInt64) : Store NearState :=
  after cfg (StorePairCaller.paid s cfg.regularOpCost 9) calleeModule len ptr

/-- Concrete advancement of the ten-instruction fragment identified in f456.
The local memory facts express the RefCell result and its vtable; they do not
assume successful indirect execution or any host invocation. -/
theorem wp_fragment (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell slice receiver vtable element : UInt32) (len ptr : UInt64)
    (callerModule calleeModule : ModuleInst) (tableAddress functionAddress inst hostAddress memoryIndex : Nat)
    (table : TableInst) (memory : Memory) (post : Post)
    (hslice : frame.locals[1]? = some (.i32 slice)) (hsize : 4 ≤ frame.locals.size)
    (hmodule : s.modules[frame.inst]? = some callerModule)
    (htableAddress : callerModule.tableAddrs[0]? = some tableAddress)
    (htable : s.tables[tableAddress]? = some table)
    (helement : table.elems[element.toNat]? = some (.func functionAddress))
    (htype : callerModule.types[4]? = some WNear.Binary.ValueReturnLeaf.signature)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function))
    (hcalleeModule : s.modules[inst]? = some calleeModule)
    (hhostAddress : calleeModule.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hcallerMemoryIndex : callerModule.memAddrs[0]? = some memoryIndex)
    (hcalleeMemoryIndex : calleeModule.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hcell : cell.toNat + 8 ≤ memory.byteSize) (hspan : slice.toNat + 8 ≤ memory.byteSize)
    (hvtable : vtable.toNat + 96 ≤ memory.byteSize)
    (hreceiverRead : readI32 memory cell.toNat = receiver)
    (hvtableRead : readI32 memory (cell.toNat + 4) = vtable)
    (helementRead : readI32 memory (vtable.toNat + 92) = element)
    (hlenRead : packed32 memory (slice.toNat + 4) = len) (hptrRead : packed32 memory slice.toNat = ptr)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (24 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest))
    (hnext : WP cfg fuel (.next (atCode (fragmentAfter cfg s calleeModule len ptr) limits base.toArray
      (dispatchFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 14) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers
      (WNear.Binary.ValueReturnDispatch.dispatch ++ code)))
      (24 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) post := by
  let prepared := StorePairCaller.paid s cfg.regularOpCost 9
  let frame' := dispatchFrame frame cell
  have hresource := StorePairCaller.paid_resources s cfg.regularOpCost 9
  have hm : prepared.modules[frame'.inst]? = some callerModule := by
    simpa only [prepared, frame', dispatchFrame] using
      (congrArg (fun st : Store NearState => st.modules[frame.inst]?) hresource).trans hmodule
  have ht : prepared.tables[tableAddress]? = some table := by
    simpa only [prepared] using (congrArg (fun st : Store NearState => st.tables[tableAddress]?) hresource).trans htable
  have hf : prepared.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function) := by
    simpa only [prepared] using (congrArg (fun st : Store NearState => st.funcs[functionAddress]?) hresource).trans hfunction
  have hcm : prepared.modules[inst]? = some calleeModule := by
    simpa only [prepared] using (congrArg (fun st : Store NearState => st.modules[inst]?) hresource).trans hcalleeModule
  have hh : prepared.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn) := by
    simpa only [prepared] using (congrArg (fun st : Store NearState => st.funcs[hostAddress]?) hresource).trans hhost
  have hmem : prepared.mems[memoryIndex]? = some memory := by
    simpa only [prepared] using (congrArg (fun st : Store NearState => st.mems[memoryIndex]?) hresource).trans hmemory
  have hcost : ValueReturnHost.cost prepared.host len.toNat = ValueReturnHost.cost s.host len.toNat := by
    simp only [prepared, StorePairCaller.paid, ValueReturnHost.cost, ValueReturnHost.dataCost, chargedStore, chargeHost]
  have hp : prepared.host.gas.Credits (15 * cfg.regularOpCost + ValueReturnHost.cost prepared.host len.toNat + rest) := by
    rw [hcost]
    exact StorePairCaller.paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))
  have hind := wp_indirect cfg extra fuel rest prepared limits base frame' callers code receiver len ptr element
    callerModule calleeModule tableAddress functionAddress inst hostAddress memoryIndex table memory post
    hm htableAddress ht helement htype hf hcm hhostAddress hh hcalleeMemoryIndex hmem hdepth
    hfixed hbound hlimit hp hnext
  rw [hcost] at hind
  have hprep := wp_prepare cfg (fuel + 5)
    (15 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) s limits base frame callers
    (.call_indirect 4 0 :: code) cell slice receiver vtable element len ptr callerModule memoryIndex memory post
    hslice hsize hmodule hcallerMemoryIndex hmemory hcell hspan hvtable hreceiverRead hvtableRead
    helementRead hlenRead hptrRead (hc.mono (by omega)) hind
  convert hprep using 1 <;> first | omega | simp only [WNear.Binary.ValueReturnDispatch.dispatch,
    List.cons_append, List.nil_append]

end WNear.Proofs.ValueReturnDispatch
