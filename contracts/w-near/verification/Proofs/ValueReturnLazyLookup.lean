import Proofs.InterfaceLazyCall
import Proofs.ValueReturnLazyReturn

/-! The actual f468 lazy path and f565 thread-local table dispatch. -/
namespace WNear.Proofs.ValueReturnLazyLookup
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open InterfaceLazyComplete (Layout)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

/-- Primitive state facts for the lazy initializer, with an explicit maximum
active caller count. No invocation or WP result is a field. -/
structure Resources (s : Store NearState) (limits : ExecLimits) (inst depth : Nat) (p : Layout) : Prop where
  module : s.modules[inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  tableIndex : p.mi.tableAddrs[0]? = some p.tableAddress
  table : s.tables[p.tableAddress]? = some p.table
  element : p.table.elems[p.location.toNat]? = some (.func p.initializerAddress)
  signature : p.mi.types[0]? = some WNear.Binary.InterfaceInitialize.signature
  initializer : s.funcs[p.initializerAddress]? = some (.wasm WNear.Binary.InterfaceInitialize.signature inst WNear.Binary.InterfaceInitialize.function)
  initializerBound : (InterfaceLazyComplete.scratch p).toNat + 8 ≤ p.memory.byteSize
  depth : depth + 1 < limits.maxCallDepth
  tail : InterfaceLazyTail.Bounds (InterfaceLazyComplete.tailLayout p)

theorem Resources.charge (s : Store NearState) (cost : Nat) (limits : ExecLimits) (inst depth : Nat) (p : Layout)
    (hr : Resources s limits inst depth p) : Resources (chargedStore s cost) limits inst depth p := by
  rcases hr with ⟨hm, hi, hg, hsp, hmi, hmem, hti, ht, he, hty, hf, hb, hd, htail⟩
  exact ⟨hm, hi, hg, hsp, hmi, hmem, hti, ht, he, hty, hf, hb, hd, htail⟩

theorem Resources.paid (s : Store NearState) (op n : Nat) (limits : ExecLimits) (inst depth : Nat) (p : Layout)
    (hr : Resources s limits inst depth p) : Resources (StorePairCaller.paid s op n) limits inst depth p := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih.charge _ op limits inst depth p

theorem Resources.weaken (s : Store NearState) (limits : ExecLimits) (inst small large : Nat) (p : Layout)
    (hr : Resources s limits inst large p) (hle : small ≤ large) : Resources s limits inst small p := by
  rcases hr with ⟨hm, hi, hg, hsp, hmi, hmem, hti, ht, he, hty, hf, hb, hd, htail⟩
  exact ⟨hm, hi, hg, hsp, hmi, hmem, hti, ht, he, hty, hf, hb, by omega, htail⟩

theorem Resources.ready (s : Store NearState) (limits : ExecLimits) (inst depth : Nat) (p : Layout)
    (hr : Resources s limits inst depth p) (frame : CallFrame) (callers : List CallFrame)
    (hinst : frame.inst = inst) (hdepth : callers.length ≤ depth)
    (hcell : frame.locals[0]? = some (.i32 p.cell)) (hlocation : frame.locals[1]? = some (.i32 p.location))
    (hsize : 5 ≤ frame.locals.size) : InterfaceLazyComplete.Ready s limits frame callers p := by
  refine ⟨?_, hr.globalIndex, hr.global, hr.sp, hr.memoryIndex, hr.memory, hr.tableIndex, hr.table, hr.element,
    hr.signature, ?_, hcell, hlocation, hsize, hr.initializerBound, ?_, hr.tail⟩
  · simpa only [hinst] using hr.module
  · simpa only [hinst] using hr.initializer
  · have hd := hr.depth; omega

def bodyAfter (s : Store NearState) (op : Nat) (p : Layout) :=
  chargedStore (InterfaceLazyCall.after (paid s op 7) op p) op

theorem bodyAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (90 * op + rest)) : (bodyAfter s op p).host.gas.Credits rest := by
  have c7 := paid_credits s op 7 (83 * op + rest) (hc.mono (by omega))
  have call := InterfaceLazyCall.after_credits_call (paid s op 7) op (op + rest) p (c7.mono (by omega))
  exact StorePair.charged_credits (InterfaceLazyCall.after (paid s op 7) op p) op rest call

/-- Actual lazy f468 body. Its explicit return bypasses both the initialized
result tail and all labels of the current callee. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 p.cell)) (hlocation : frame.locals[1]? = some (.i32 p.location))
    (harity : frame.arity = 1) (hheight : frame.height = base.length)
    (hr : Resources s limits frame.inst (callers.length + 2) p)
    (haddress : p.mi.funcAddrs[467]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function))
    (hbound : p.cell.toNat + 4 ≤ p.memory.byteSize) (hstatus : readI32 p.memory p.cell.toNat ≠ 1)
    (hc : s.host.gas.Credits (90 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyAfter s cfg.regularOpCost p) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 74) (.next (atCode s limits base.toArray frame (caller :: callers)
      (WNear.Binary.ValueReturnThreadLocal.body ++ code))) (90 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let block := emptyBlockFrame frame base.length (WNear.Binary.ValueReturnThreadLocal.resultTail ++ code)
  let prepared := paid s op 7
  let returned := InterfaceLazyCall.after prepared op p
  have cp := paid_credits s op 7 (83 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cr : returned.host.gas.Credits (op + rest) := InterfaceLazyCall.after_credits_call prepared op (op + rest) p (cp.mono (by omega))
  have arity : [Value.i32 (p.cell + 4)].length = block.arity := by simpa only [block, emptyBlockFrame, List.length_cons, List.length_nil] using harity.symm
  have height : block.height = base.length := by simpa only [block, emptyBlockFrame] using hheight
  have returnRule := wp_return_wasm cfg fuel rest returned limits base [.i32 (p.cell + 4)] block caller callers [] post arity height cr
  have returnNext : WP cfg fuel (.next (atCode (chargedStore returned op) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray caller callers caller.code)) rest post := by
    simpa only [bodyAfter, prepared, returned, op] using hnext
  have returnedStep := returnRule returnNext
  have resources := hr.paid s op 7 limits frame.inst (callers.length + 2) p
  have ready : InterfaceLazyCall.Ready prepared limits block (caller :: callers) base [.return] p := by
    apply resources.ready prepared limits frame.inst (callers.length + 2) p
      (InterfaceLazyCall.calleeFrame block.inst base.length p) ({block with code := [.return]} :: caller :: callers)
    · rfl
    · simp only [List.length_cons]; omega
    · rfl
    · rfl
    · simp [InterfaceLazyCall.calleeFrame]
  have function : prepared.funcs[address]? = some (.wasm WNear.Binary.InterfaceLazy.signature block.inst WNear.Binary.InterfaceLazy.function) := by
    simpa only [prepared, block, emptyBlockFrame, paid, chargedStore] using hfunction
  have callRule := InterfaceLazyCall.wp_call cfg (fuel + 1) (op + rest) prepared limits base block (caller :: callers) [.return] p address post
    ready haddress function (cp.mono (by dsimp [op]; omega))
  have returnNext' : WP cfg (fuel + 1) (.next (atCode returned limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray block (caller :: callers) [.return])) (op + rest) post := by
    simpa only [op] using returnedStep
  have call := callRule returnNext'
  have cell : block.locals[0]? = some (.i32 p.cell) := hcell
  have location : block.locals[1]? = some (.i32 p.location) := hlocation
  have getLocation := wp_local_get cfg (fuel + 66) (83 * op + rest) (paid s op 6) limits (base.toArray.push (.i32 p.cell)) block
    (caller :: callers) [.call 467, .return] 1 (.i32 p.location) post location
    (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega)))
  have callNext : WP cfg (fuel + 66) (.next (atCode prepared limits
      ((base.toArray.push (.i32 p.cell)).push (.i32 p.location)) block (caller :: callers) [.call 467, .return])) (83 * op + rest) post := by
    rw [show 82 * cfg.regularOpCost + (op + rest) = 83 * op + rest by dsimp [op]; omega] at call
    simpa using call
  have getLocationNext := getLocation callNext
  have getCell := wp_local_get cfg (fuel + 67) (84 * op + rest) (paid s op 5) limits base.toArray block (caller :: callers)
    [.local_get 1, .call 467, .return] 0 (.i32 p.cell) post cell (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega)))
  have getCellNext := getCell (by
    rw [show cfg.regularOpCost + (83 * op + rest) = 84 * op + rest by dsimp [op]; omega] at getLocationNext
    exact getLocationNext)
  have guardRule := wp_lazy_guard cfg (fuel + 68) (85 * op + rest) s limits base.toArray block (caller :: callers)
    WNear.Binary.ValueReturnThreadLocal.lazyTail p.cell p.mi p.memoryIndex p.memory post hcell hr.module hr.memoryIndex hr.memory hbound hstatus
    (hc.mono (by dsimp [op]; omega))
  have lazyNext : WP cfg (fuel + 68) (.next (atCode (paid s op 5) limits base.toArray block (caller :: callers)
      WNear.Binary.ValueReturnThreadLocal.lazyTail)) (85 * op + rest) post := by
    rw [show cfg.regularOpCost + (84 * op + rest) = 85 * op + rest by dsimp [op]; omega] at getCellNext
    exact getCellNext
  have guard := guardRule lazyNext
  have blockRule := wp_block_empty cfg (fuel + 73) (90 * op + rest) s limits base.toArray frame (caller :: callers)
    (WNear.Binary.ValueReturnThreadLocal.guard ++ WNear.Binary.ValueReturnThreadLocal.lazyTail)
    (WNear.Binary.ValueReturnThreadLocal.resultTail ++ code) post hc
  have blockNext : WP cfg (fuel + 73) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.toArray.size (WNear.Binary.ValueReturnThreadLocal.resultTail ++ code)) (caller :: callers)
      (WNear.Binary.ValueReturnThreadLocal.guard ++ WNear.Binary.ValueReturnThreadLocal.lazyTail))) (90 * op + rest) post := by
    rw [show 5 * cfg.regularOpCost + (85 * op + rest) = 90 * op + rest by dsimp [op]; omega] at guard
    simpa only [block, List.size_toArray, Nat.add_assoc, Nat.reduceAdd] using guard
  have result := blockRule blockNext
  simpa only [WNear.Binary.ValueReturnThreadLocal.body, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := bodyAfter (entered s op) op p

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (100 * op + rest)) : (callAfter s op p).host.gas.Credits rest := by
  have hop := StorePair.charged_credits s op (9 * op + (90 * op + rest)) (hc.mono (by omega))
  have activation := StorePair.charged_credits (chargedStore s op) (9 * op) (90 * op + rest) hop
  exact bodyAfter_credits (entered s op) op rest p activation

/-- The real f468 local call, taking its lazy branch and returning directly
through the explicit return instruction. -/
theorem wp_call_lazy (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address lazyAddress : Nat) (post : Post)
    (hr : Resources s limits frame.inst (callers.length + 2) p)
    (haddress : p.mi.funcAddrs[468]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function))
    (hlazyAddress : p.mi.funcAddrs[467]? = some lazyAddress)
    (hlazy : s.funcs[lazyAddress]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function))
    (hb : p.cell.toNat + 4 ≤ p.memory.byteSize) (hstatus : readI32 p.memory p.cell.toNat ≠ 1)
    (hc : s.host.gas.Credits (100 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 75) (.next (atCode s limits (base ++ [Value.i32 p.cell, .i32 p.location]).toArray frame callers
      (.call 468 :: code))) (100 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[.i32 p.cell, .i32 p.location], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have r : Resources active limits leaf.inst (callers.length + 2) p := (hr.charge s op limits frame.inst (callers.length + 2) p).charge _ (9 * op) limits frame.inst (callers.length + 2) p
  have cp : active.host.gas.Credits (90 * op + rest) := by
    have hop := StorePair.charged_credits s op (9 * op + (90 * op + rest)) (hc.mono (by dsimp [op]; omega))
    exact StorePair.charged_credits (chargedStore s op) (9 * op) (90 * op + rest) hop
  have lazy : active.funcs[lazyAddress]? = some (.wasm WNear.Binary.InterfaceLazy.signature leaf.inst WNear.Binary.InterfaceLazy.function) := by
    simpa only [active, entered, chargedStore, leaf] using hlazy
  have bodyRule := wp_body cfg fuel rest active limits base leaf saved callers [] p lazyAddress post rfl rfl rfl rfl r
    hlazyAddress lazy hb hstatus cp
  have bodyNext : WP cfg fuel (.next (atCode (bodyAfter active op p) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray saved callers saved.code)) rest post := by
    simpa only [callAfter, active, saved, atCode, op] using hnext
  have body := bodyRule bodyNext
  have activation : activationGas op (wasmLocals WNear.Binary.ValueReturnThreadLocal.function [.i32 p.cell, .i32 p.location]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.ValueReturnThreadLocal.function]
  have depth : callers.length + 1 < limits.maxCallDepth := by have hd := hr.depth; omega
  have callRule := wp_call_wasm cfg (fuel + 74) (90 * op + rest) s limits base [.i32 p.cell, .i32 p.location] frame callers code
    468 address p.mi WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function post hr.module haddress hfunction rfl depth
  rw [activation] at callRule
  have next : WP cfg (fuel + 74) (.next (wasmCallee active limits base frame callers code WNear.Binary.ValueReturnThreadLocal.signature frame.inst
      WNear.Binary.ValueReturnThreadLocal.function [.i32 p.cell, .i32 p.location])) (90 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.ValueReturnThreadLocal.function, WNear.Binary.ValueReturnThreadLocal.signature,
      atCode, leaf, saved, List.map_nil, List.append_nil, Array.append_empty, List.length_cons, List.length_nil, Nat.reduceAdd, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (9 * op + (90 * op + rest)) = 100 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

def lookupAfter (s : Store NearState) (op : Nat) (p : Layout) := callAfter (paid s op 2) op p

theorem lookupAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (102 * op + rest)) : (lookupAfter s op p).host.gas.Credits rest :=
  callAfter_credits (paid s op 2) op rest p (paid_credits s op 2 _ (hc.mono (by omega)))

/-- Actual f565 constants and its real lazy f468 invocation. -/
theorem wp_lookup_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address lazyAddress : Nat) (post : Post)
    (hr : Resources s limits frame.inst (callers.length + 2) p)
    (hcell : p.cell = 1074900) (hlocation : p.location = 106)
    (haddress : p.mi.funcAddrs[468]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function))
    (hlazyAddress : p.mi.funcAddrs[467]? = some lazyAddress)
    (hlazy : s.funcs[lazyAddress]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function))
    (hb : p.cell.toNat + 4 ≤ p.memory.byteSize) (hstatus : readI32 p.memory p.cell.toNat ≠ 1)
    (hc : s.host.gas.Credits (102 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (lookupAfter s cfg.regularOpCost p) limits
      (base ++ [Value.i32 1074904]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 77) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnThreadLocal.lookupBody ++ code))) (102 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let prepared := paid s op 2
  have resources := hr.paid s op 2 limits frame.inst (callers.length + 2) p
  have helper : prepared.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function) := by
    simpa only [prepared, paid, chargedStore] using hfunction
  have lazy : prepared.funcs[lazyAddress]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function) := by
    simpa only [prepared, paid, chargedStore] using hlazy
  have cp := paid_credits s op 2 (100 * op + rest) (hc.mono (by dsimp [op]; omega))
  have callRule := wp_call_lazy cfg fuel rest prepared limits base frame callers code p address lazyAddress post resources haddress helper hlazyAddress lazy hb hstatus cp
  have next : WP cfg fuel (.next (atCode (callAfter prepared op p) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray frame callers code)) rest post := by
    simpa only [lookupAfter, prepared, hcell, op, show (1074900 : UInt32) + 4 = 1074904 by decide] using hnext
  have call := callRule next
  have constLocation := wp_i32_const cfg (fuel + 75) (100 * op + rest) (paid s op 1) limits (base.toArray.push (.i32 1074900)) frame callers
    (.call 468 :: code) 106 post (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega)))
  have callNext : WP cfg (fuel + 75) (.next (atCode prepared limits ((base.toArray.push (.i32 1074900)).push (.i32 106)) frame callers
      (.call 468 :: code))) (100 * op + rest) post := by
    simpa [hcell, hlocation, prepared, op] using call
  have location := constLocation callNext
  have constCell := wp_i32_const cfg (fuel + 76) (101 * op + rest) s limits base.toArray frame callers
    (.i32_const 106 :: .call 468 :: code) 1074900 post (hc.mono (by dsimp [op]; omega))
  have cellNext : WP cfg (fuel + 76) (.next (atCode (paid s op 1) limits (base.toArray.push (.i32 1074900)) frame callers
      (.i32_const 106 :: .call 468 :: code))) (101 * op + rest) post := by
    rw [show cfg.regularOpCost + (100 * op + rest) = 101 * op + rest by dsimp [op]; omega] at location
    exact location
  have result := constCell cellNext
  rw [show cfg.regularOpCost + (101 * op + rest) = 102 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [WNear.Binary.ValueReturnThreadLocal.lookupBody, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using result

def indirectEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (8 * op)
def indirectAfter (s : Store NearState) (op : Nat) (p : Layout) := lookupAfter (indirectEntered s op) op p

theorem indirectAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (111 * op + rest)) : (indirectAfter s op p).host.gas.Credits rest := by
  have hop := StorePair.charged_credits s op (8 * op + (102 * op + rest)) (hc.mono (by omega))
  have activation := StorePair.charged_credits (chargedStore s op) (8 * op) (102 * op + rest) hop
  exact lookupAfter_credits (indirectEntered s op) op rest p activation

/-- The actual type-one table dispatch reaches f565, then lazy f468 and f467,
whose own table call executes the real zero initializer. Every link is a
primitive table/type/function fact, with no callee execution premise. -/
theorem wp_indirect_lookup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address helperAddress lazyAddress : Nat)
    (element : UInt32) (post : Post)
    (hr : Resources s limits frame.inst (callers.length + 3) p)
    (hcell : p.cell = 1074900) (hlocation : p.location = 106)
    (helement : p.table.elems[element.toNat]? = some (.func address))
    (htype : p.mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst WNear.Binary.ValueReturnThreadLocal.lookupFunction))
    (hhelperAddress : p.mi.funcAddrs[468]? = some helperAddress)
    (hhelper : s.funcs[helperAddress]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function))
    (hlazyAddress : p.mi.funcAddrs[467]? = some lazyAddress)
    (hlazy : s.funcs[lazyAddress]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function))
    (hb : p.cell.toNat + 4 ≤ p.memory.byteSize) (hstatus : readI32 p.memory p.cell.toNat ≠ 1)
    (hc : s.host.gas.Credits (111 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (indirectAfter s cfg.regularOpCost p) limits
      (base ++ [Value.i32 1074904]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 79) (.next (atCode s limits (base.toArray.push (.i32 element)) frame callers
      (.call_indirect 1 0 :: code))) (111 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := indirectEntered s op
  let leaf : CallFrame := {locals := #[], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have r : Resources active limits leaf.inst ((saved :: callers).length + 2) p := by
    have resources := (hr.charge s op limits frame.inst (callers.length + 3) p).charge _ (8 * op) limits frame.inst (callers.length + 3) p
    simpa only [active, indirectEntered, leaf, List.length_cons, Nat.add_assoc, Nat.reduceAdd] using resources
  have cp : active.host.gas.Credits (102 * op + rest) := by
    have hop := StorePair.charged_credits s op (8 * op + (102 * op + rest)) (hc.mono (by dsimp [op]; omega))
    exact StorePair.charged_credits (chargedStore s op) (8 * op) (102 * op + rest) hop
  have cf := indirectAfter_credits s op rest p hc
  have leaveRule := wp_leave_wasm cfg fuel rest (indirectAfter s op p) limits base [Value.i32 1074904] leaf saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (indirectAfter s op p) limits (base ++ [Value.i32 1074904]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have leave := leaveRule leaveNext
  have helper : active.funcs[helperAddress]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature leaf.inst WNear.Binary.ValueReturnThreadLocal.function) := by
    simpa only [active, indirectEntered, chargedStore, leaf] using hhelper
  have lazy : active.funcs[lazyAddress]? = some (.wasm WNear.Binary.InterfaceLazy.signature leaf.inst WNear.Binary.InterfaceLazy.function) := by
    simpa only [active, indirectEntered, chargedStore, leaf] using hlazy
  have bodyRule := wp_lookup_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] p helperAddress lazyAddress post r hcell hlocation
    hhelperAddress helper hlazyAddress lazy hb hstatus cp
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (lookupAfter active op p) limits (base ++ [Value.i32 1074904]).toArray leaf (saved :: callers) [])) rest post := by
    simpa only [indirectAfter, active, op] using leave
  have body := bodyRule bodyNext
  have activation : activationGas op (wasmLocals WNear.Binary.ValueReturnThreadLocal.lookupFunction []) = 8 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.ValueReturnThreadLocal.lookupFunction]
  have depth : callers.length + 1 < limits.maxCallDepth := by have hd := hr.depth; omega
  have callRule := wp_call_indirect_wasm cfg ((fuel + 1) + 77) (102 * op + rest) s limits base [] frame callers code 1 0 p.tableAddress address element p.table p.mi
    WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst WNear.Binary.ValueReturnThreadLocal.lookupFunction post hr.module hr.tableIndex hr.table helement htype hfunction rfl depth
  rw [activation] at callRule
  have next : WP cfg ((fuel + 1) + 77) (.next (wasmCallee active limits base frame callers code WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst WNear.Binary.ValueReturnThreadLocal.lookupFunction [])) (102 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.ValueReturnThreadLocal.lookupFunction, WNear.Binary.ValueReturnThreadLocal.lookupSignature,
      atCode, leaf, saved, List.map_nil, List.append_nil, List.nil_append, Array.append_empty, List.length_cons, List.length_nil, Nat.reduceAdd, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (8 * op + (102 * op + rest)) = 111 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [List.append_nil, Nat.add_assoc, Nat.reduceAdd] using result

end WNear.Proofs.ValueReturnLazyLookup
