import Binary.ValueReturnThreadLocal
import Proofs.ValueReturnBorrow
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredIndirectCall

/-! Actual initialized thread-local lookup. The lazy initialization path is
skipped only after the real status load and comparison. -/
namespace WNear.Proofs.ValueReturnThreadLocal
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

/-- The status-one path of actual f468 reads memory and returns ptr+4.
The lazy f467 call and early return are not executed. -/
theorem wp_initialized (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (ptr : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hptr : frame.locals[0]? = some (.i32 ptr))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : ptr.toNat + 4 ≤ memory.byteSize)
    (hstatus : readI32 memory ptr.toNat = 1)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits
      (stack.push (.i32 (ptr + 4))) frame callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnThreadLocal.body ++ code))) (8 * cfg.regularOpCost + rest) post := by
  let blockFrame := emptyBlockFrame frame stack.size (WNear.Binary.ValueReturnThreadLocal.resultTail ++ code)
  apply wp_block_empty cfg (fuel + 8) _ s limits stack frame callers _ _ post hc
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 7) _ s limits stack blockFrame callers _ 0 (.i32 ptr) post hptr (hc.mono (by omega))
  have hm : (paid s cfg.regularOpCost 1).modules[blockFrame.inst]? = some mi := hmodule
  have hmem : (paid s cfg.regularOpCost 1).mems[index]? = some memory := hmemory
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 6) _ (paid s cfg.regularOpCost 1) limits stack blockFrame callers _
    {align := 2, offset := 0} ptr mi index memory post hm hindex hmem (by simpa using hbound)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  simp only [Nat.add_zero, hstatus]
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 5) _ (paid s cfg.regularOpCost 2) limits _ blockFrame callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_relop cfg (fuel + 4) _ (paid s cfg.regularOpCost 3) limits stack blockFrame callers _ .eq 1 1 post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  change WP cfg (fuel + 4) (.next (atCode (paid s cfg.regularOpCost 4) limits (stack.push (.i32 1))
    blockFrame callers (.br_if 0 :: WNear.Binary.ValueReturnThreadLocal.lazyTail))) (4 * cfg.regularOpCost + rest) post
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_br_if_block_nonzero cfg (fuel + 3) _ (paid s cfg.regularOpCost 4) limits stack frame callers
    (WNear.Binary.ValueReturnThreadLocal.resultTail ++ code) WNear.Binary.ValueReturnThreadLocal.lazyTail 1 post (by decide)
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 5) limits stack frame callers _ 0 (.i32 ptr) post hptr
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 6) limits _ frame callers _ 4 post
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  apply wp_i32_add cfg fuel rest (paid s cfg.regularOpCost 7) limits stack frame callers code ptr 4 post
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  · exact hnext

def entered (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (9 * op)

def callAfter (s : Store NearState) (op : Nat) : Store NearState := paid (entered s op) op 8

/-- Full actual f468 local call on the initialized path, including typed return. -/
theorem wp_call_initialized (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (ptr location : UInt32) (address : Nat) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[468]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst
      WNear.Binary.ValueReturnThreadLocal.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : ptr.toNat + 4 ≤ memory.byteSize) (hstatus : readI32 memory ptr.toNat = 1)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (18 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost) limits
      (base ++ [Value.i32 (ptr + 4)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 11) (.next (atCode s limits (base ++ [Value.i32 ptr, .i32 location]).toArray
      frame callers (.call 468 :: code))) (18 * cfg.regularOpCost + rest) post := by
  let active := entered s cfg.regularOpCost
  let leaf : CallFrame := {locals := #[Value.i32 ptr, .i32 location], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code := code}
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s cfg.regularOpCost _ h0
  have h2 : active.host.gas.Credits (8 * cfg.regularOpCost + rest) :=
    WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) (9 * cfg.regularOpCost) _ h1
  have hf : (callAfter s cfg.regularOpCost).host.gas.Credits rest := paid_credits active cfg.regularOpCost 8 rest h2
  have leave := wp_leave_wasm cfg fuel rest (callAfter s cfg.regularOpCost) limits base [Value.i32 (ptr + 4)]
    leaf saved callers post rfl rfl rfl hf hnext
  have hs : (base ++ [Value.i32 (ptr + 4)]).toArray = base.toArray.push (.i32 (ptr + 4)) := by
    apply Array.toList_inj.mp; simp
  have next : WP cfg (fuel + 1) (.next (atCode (paid active cfg.regularOpCost 8) limits
      (base.toArray.push (.i32 (ptr + 4))) leaf (saved :: callers) [])) rest post := by
    simpa only [hs, callAfter, active] using leave
  have hm : active.modules[leaf.inst]? = some mi := hmodule
  have hmem : active.mems[index]? = some memory := hmemory
  have body := wp_initialized cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) []
    ptr mi index memory post rfl hm hindex hmem hbound hstatus h2 next
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.ValueReturnThreadLocal.function [Value.i32 ptr, .i32 location]) = 9 * cfg.regularOpCost := by
    simp [activationGas, wasmLocals, WNear.Binary.ValueReturnThreadLocal.function]
  have rule := wp_call_wasm cfg ((fuel + 1) + 9) (8 * cfg.regularOpCost + rest) s limits base
    [Value.i32 ptr, .i32 location] frame callers code 468 address mi WNear.Binary.ValueReturnThreadLocal.signature
    frame.inst WNear.Binary.ValueReturnThreadLocal.function post hmodule haddress hfunction rfl hdepth
  rw [activation] at rule
  have nextBody : WP cfg ((fuel + 1) + 9) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function
      [Value.i32 ptr, .i32 location])) (8 * cfg.regularOpCost + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.ValueReturnThreadLocal.function,
      WNear.Binary.ValueReturnThreadLocal.signature, atCode, leaf, saved, List.map_nil,
      List.append_nil, Array.append_empty, List.length_cons, List.length_nil] using body
  have result := rule h0 nextBody
  have budget : cfg.regularOpCost + (9 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest)) =
      18 * cfg.regularOpCost + rest := by omega
  rw [budget] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

def lookupAfter (s : Store NearState) (op : Nat) : Store NearState := callAfter (paid s op 2) op

/-- Actual f565 body prepares the constants and executes f468. -/
theorem wp_lookup_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (address : Nat) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[468]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst
      WNear.Binary.ValueReturnThreadLocal.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : 1074900 + 4 ≤ memory.byteSize) (hstatus : readI32 memory 1074900 = 1)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (20 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (lookupAfter s cfg.regularOpCost) limits
      (base ++ [Value.i32 1074904]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnThreadLocal.lookupBody ++ code))) (20 * cfg.regularOpCost + rest) post := by
  rw [show 20 * cfg.regularOpCost + rest = cfg.regularOpCost + (19 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 12) _ s limits base.toArray frame callers _ 1074900 post (hc.mono (by omega))
  rw [show 19 * cfg.regularOpCost + rest = cfg.regularOpCost + (18 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 11) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 106 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hm : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := hmodule
  have hf : (paid s cfg.regularOpCost 2).funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature
      frame.inst WNear.Binary.ValueReturnThreadLocal.function) := hfunction
  have hmem : (paid s cfg.regularOpCost 2).mems[index]? = some memory := hmemory
  have hn : WP cfg fuel (.next (atCode (callAfter (paid s cfg.regularOpCost 2) cfg.regularOpCost) limits
      (base ++ [Value.i32 ((1074900 : UInt32) + 4)]).toArray frame callers code)) rest post := hnext
  have hcall := wp_call_initialized cfg fuel rest (paid s cfg.regularOpCost 2) limits base frame callers code
    1074900 106 address mi index memory post hm haddress hf hindex hmem hbound hstatus hdepth
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hn
  have hs : (base ++ [Value.i32 1074900, .i32 106]).toArray =
      (base.toArray.push (.i32 1074900)).push (.i32 106) := by
    apply Array.toList_inj.mp; simp
  simpa only [hs, paid, List.append] using hcall

theorem callAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (18 * op + rest)) : (callAfter s op).host.gas.Credits rest := by
  have h : s.host.gas.Credits (op + (9 * op + (8 * op + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h
  have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s op) (9 * op) _ h1
  exact paid_credits (entered s op) op 8 rest h2

def indirectEntered (s : Store NearState) (op : Nat) : Store NearState :=
  chargedStore (chargedStore s op) (8 * op)

def indirectAfter (s : Store NearState) (op : Nat) : Store NearState := lookupAfter (indirectEntered s op) op

/-- The real type-1 indirect call reaches f565, calls initialized f468, and
returns the concrete thread-local interface pointer to the original caller. -/
theorem wp_indirect_lookup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (tableAddress address helperAddress index : Nat)
    (element : UInt32) (table : TableInst) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (htableAddress : mi.tableAddrs[0]? = some tableAddress)
    (htable : s.tables[tableAddress]? = some table) (helement : table.elems[element.toNat]? = some (.func address))
    (htype : mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst
      WNear.Binary.ValueReturnThreadLocal.lookupFunction))
    (hhelperAddress : mi.funcAddrs[468]? = some helperAddress)
    (hhelper : s.funcs[helperAddress]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst
      WNear.Binary.ValueReturnThreadLocal.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : 1074900 + 4 ≤ memory.byteSize) (hstatus : readI32 memory 1074900 = 1)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (29 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (indirectAfter s cfg.regularOpCost) limits
      (base ++ [Value.i32 1074904]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits (base.toArray.push (.i32 element)) frame callers
      (.call_indirect 1 0 :: code))) (29 * cfg.regularOpCost + rest) post := by
  let active := indirectEntered s cfg.regularOpCost
  let leaf : CallFrame := {locals := #[], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code := code}
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (8 * cfg.regularOpCost + (20 * cfg.regularOpCost + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s cfg.regularOpCost _ h0
  have h2 : active.host.gas.Credits (20 * cfg.regularOpCost + rest) :=
    WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) (8 * cfg.regularOpCost) _ h1
  have hp : (paid active cfg.regularOpCost 2).host.gas.Credits (18 * cfg.regularOpCost + rest) :=
    paid_credits active cfg.regularOpCost 2 _ (h2.mono (by omega))
  have hf : (indirectAfter s cfg.regularOpCost).host.gas.Credits rest := callAfter_credits _ _ rest hp
  have leave := wp_leave_wasm cfg fuel rest (indirectAfter s cfg.regularOpCost) limits base [Value.i32 1074904]
    leaf saved callers post rfl rfl rfl hf hnext
  have hm : active.modules[leaf.inst]? = some mi := hmodule
  have hh : active.funcs[helperAddress]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature leaf.inst
      WNear.Binary.ValueReturnThreadLocal.function) := hhelper
  have hmem : active.mems[index]? = some memory := hmemory
  have hd : (saved :: callers).length + 1 < limits.maxCallDepth := by simp only [List.length_cons]; omega
  have body := wp_lookup_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] helperAddress
    mi index memory post hm hhelperAddress hh hindex hmem hbound hstatus hd h2 leave
  have activation : activationGas cfg.regularOpCost (wasmLocals WNear.Binary.ValueReturnThreadLocal.lookupFunction []) =
      8 * cfg.regularOpCost := by simp [activationGas, wasmLocals, WNear.Binary.ValueReturnThreadLocal.lookupFunction]
  have hd0 : callers.length + 1 < limits.maxCallDepth := by omega
  have rule := wp_call_indirect_wasm cfg ((fuel + 1) + 13) (20 * cfg.regularOpCost + rest) s limits base [] frame callers
    code 1 0 tableAddress address element table mi WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst
    WNear.Binary.ValueReturnThreadLocal.lookupFunction post hmodule htableAddress htable helement htype hfunction rfl hd0
  rw [activation] at rule
  have nextBody : WP cfg ((fuel + 1) + 13) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst WNear.Binary.ValueReturnThreadLocal.lookupFunction []))
      (20 * cfg.regularOpCost + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.ValueReturnThreadLocal.lookupFunction,
      WNear.Binary.ValueReturnThreadLocal.lookupSignature, atCode, leaf, saved, List.map_nil,
      List.append_nil, List.nil_append, Array.append_empty, List.length_cons, List.length_nil] using body
  have result := rule h0 nextBody
  have budget : cfg.regularOpCost + (8 * cfg.regularOpCost + (20 * cfg.regularOpCost + rest)) =
      29 * cfg.regularOpCost + rest := by omega
  rw [budget] at result
  simpa only [List.append_nil, Nat.add_assoc, Nat.reduceAdd] using result

theorem indirectAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (29 * op + rest)) : (indirectAfter s op).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (op + (8 * op + (20 * op + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s op) (8 * op) _ h1
  have hp := paid_credits (indirectEntered s op) op 2 (18 * op + rest) (h2.mono (by omega))
  exact callAfter_credits _ op rest hp

end WNear.Proofs.ValueReturnThreadLocal
