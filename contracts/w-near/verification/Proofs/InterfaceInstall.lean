import Binary.InterfaceInstall
import Proofs.ValueReturnBorrow
import NearVM.MeteredWasmCall
import NearVM.MeteredI32MemoryRules
import Proofs.ValueReturnOuterLayout

/-! Actual interface-drop guard on its empty-record branch. A nonempty record
executes f465 and is deliberately outside this branch contract. -/
namespace WNear.Proofs.InterfaceInstall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384

/-- The empty old interface skips the actual drop call after its real load. -/
theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 pointer))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : pointer.toNat + 4 ≤ memory.byteSize)
    (hempty : readI32 memory pointer.toNat = 0)
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers (WNear.Binary.InterfaceInstall.guardBody ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  let blockFrame := emptyBlockFrame frame stack.size code
  apply wp_block_empty cfg (fuel + 4) _ s limits stack frame callers _ code post hc
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack blockFrame callers _ 0 (.i32 pointer) post hlocal (hc.mono (by omega))
  have hm : (paid s cfg.regularOpCost 1).modules[blockFrame.inst]? = some mi := hmodule
  have hmem : (paid s cfg.regularOpCost 1).mems[index]? = some memory := hmemory
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits stack blockFrame callers _
    {align := 2, offset := 0} pointer mi index memory post hm hindex hmem (by simpa using hbound)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  simp only [Nat.add_zero, hempty]
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits stack blockFrame callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  change WP cfg (fuel + 1) (.next (atCode (paid s cfg.regularOpCost 3) limits (stack.push (.i32 1))
    blockFrame callers [.br_if 0, .local_get 0, .call 465])) (cfg.regularOpCost + rest) post
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code
    [.local_get 0, .call 465] 1 post (by decide)
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  · exact hnext

def guardEntry (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def guardAfter (s : Store NearState) (op : Nat) := paid (guardEntry s op) op 4

/-- The complete real f464 call on the zero old-receiver path, including
activation and normal void return, with arbitrary saved callers and operands. -/
theorem wp_call_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (address : Nat) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (haddress : mi.funcAddrs[464]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceInstall.guardSignature frame.inst
      WNear.Binary.InterfaceInstall.guardFunction))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : pointer.toNat + 4 ≤ memory.byteSize) (hempty : readI32 memory pointer.toNat = 0)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (14 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (guardAfter s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits (base ++ [Value.i32 pointer]).toArray
      frame callers (.call 464 :: code))) (14 * cfg.regularOpCost + rest) post := by
  let active := guardEntry s cfg.regularOpCost
  let leaf : CallFrame := {locals := #[Value.i32 pointer], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code := code}
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s cfg.regularOpCost _ h0
  have h2 : active.host.gas.Credits (4 * cfg.regularOpCost + rest) :=
    WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) (9 * cfg.regularOpCost) _ h1
  have hf : (guardAfter s cfg.regularOpCost).host.gas.Credits rest := paid_credits active cfg.regularOpCost 4 rest h2
  have hn : WP cfg fuel (.next (atCode (guardAfter s cfg.regularOpCost) limits
      (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [List.append_nil, saved, atCode] using hnext
  have leave := wp_leave_wasm cfg fuel rest (guardAfter s cfg.regularOpCost) limits base []
    leaf saved callers post rfl rfl rfl hf hn
  have next : WP cfg (fuel + 1) (.next (atCode (paid active cfg.regularOpCost 4) limits
      base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [List.append_nil, guardAfter, active] using leave
  have hm : active.modules[leaf.inst]? = some mi := hmodule
  have hmem : active.mems[index]? = some memory := hmemory
  have body := wp_guard cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) []
    pointer mi index memory post rfl hm hindex hmem hbound hempty h2 next
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.InterfaceInstall.guardFunction [Value.i32 pointer]) = 9 * cfg.regularOpCost := by
    simp [activationGas, wasmLocals, WNear.Binary.InterfaceInstall.guardFunction]
  have rule := wp_call_wasm cfg ((fuel + 1) + 5) (4 * cfg.regularOpCost + rest) s limits base
    [Value.i32 pointer] frame callers code 464 address mi WNear.Binary.InterfaceInstall.guardSignature
    frame.inst WNear.Binary.InterfaceInstall.guardFunction post hmodule haddress hfunction rfl hdepth
  rw [activation] at rule
  have nextBody : WP cfg ((fuel + 1) + 5) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.InterfaceInstall.guardSignature frame.inst WNear.Binary.InterfaceInstall.guardFunction [Value.i32 pointer]))
      (4 * cfg.regularOpCost + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.InterfaceInstall.guardFunction,
      WNear.Binary.InterfaceInstall.guardSignature, WNear.Binary.InterfaceInstall.guardBody, atCode, leaf, saved,
      List.map_nil, List.append_nil, Array.append_empty, List.length_cons, List.length_nil] using body
  have result := rule h0 nextBody
  rw [show cfg.regularOpCost + (9 * cfg.regularOpCost + (4 * cfg.regularOpCost + rest)) =
      14 * cfg.regularOpCost + rest by omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

/-- Sufficient original credit pays both entry charges and the four body ops. -/
theorem guardAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (14 * op + rest)) : (guardAfter s op).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (op + (9 * op + (4 * op + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s op) (9 * op) _ h1
  exact paid_credits (guardEntry s op) op 4 rest h2

/-- The empty-record guard changes no guest resource. -/
theorem guardAfter_resources (s : Store NearState) (op : Nat) :
    {guardAfter s op with host := s.host} = s := by
  simp only [guardAfter, guardEntry, paid, chargedStore]

/-- Its functional host fields also stay unchanged. -/
theorem guardAfter_host (s : Store NearState) (op : Nat) :
    {(guardAfter s op).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [guardAfter, guardEntry, paid, chargedStore, chargeHost]

/-- The actual f520 wrapper pushes the static interface address and both
original arguments before invoking f463. -/
theorem wp_wrapper_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (receiver vtable : UInt32) (post : Post)
    (hr : frame.locals[0]? = some (.i32 receiver)) (hv : frame.locals[1]? = some (.i32 vtable))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (((stack.push (.i32 1055020)).push (.i32 receiver)).push (.i32 vtable)) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.i32_const 1055020, .local_get 0, .local_get 1] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ s limits stack frame callers _ 1055020 post (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 (.i32 receiver) post hr
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_local_get cfg fuel rest (paid s cfg.regularOpCost 2) limits _ frame callers code 1 (.i32 vtable) post hv
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

/-- Exact two stores of the setter's install fragment, in deployed order. -/
def installMemory (memory : Memory) (address : Nat) (receiver vtable : UInt32) : Memory :=
  writeI32 (writeI32 memory (address + 4) vtable) address receiver

/-- Adjacent setter words are recovered exactly; outside the eight-byte
record every original byte is retained. No alignment premise is needed. -/
theorem installMemory_spec (memory : Memory) (address : Nat) (receiver vtable : UInt32)
    (hwf : memory.wf) (hspan : address + 8 ≤ memory.byteSize) :
    (installMemory memory address receiver vtable).wf ∧
    (installMemory memory address receiver vtable).byteSize = memory.byteSize ∧
    (installMemory memory address receiver vtable).max = memory.max ∧
    readI32 (installMemory memory address receiver vtable) address = receiver ∧
    readI32 (installMemory memory address receiver vtable) (address + 4) = vtable ∧
    ∀ j, (j < address ∨ address + 8 ≤ j) →
      (installMemory memory address receiver vtable).read8 j = memory.read8 j := by
  have hfirst := writeI32_spec memory (address + 4) vtable hwf (by omega)
  have hsecondBound : address + 4 ≤ (writeI32 memory (address + 4) vtable).byteSize := by
    rw [hfirst.2.1]; omega
  have hsecond := writeI32_spec (writeI32 memory (address + 4) vtable) address receiver hfirst.1 hsecondBound
  refine ⟨hsecond.1, hsecond.2.1.trans hfirst.2.1, hsecond.2.2.1.trans hfirst.2.2.1, ?_, ?_, ?_⟩
  · apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw [installMemory, hsecond.2.2.2]
    have hin : address ≤ address + i ∧ address + i < address + 4 := by omega
    simp [hin]
  · apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw [installMemory, hsecond.2.2.2, hfirst.2.2.2]
    have hout : ¬ (address ≤ address + 4 + i ∧ address + 4 + i < address + 4) := by omega
    have hin : address + 4 ≤ address + 4 + i ∧ address + 4 + i < address + 4 + 4 := by omega
    simp [hout, hin]
  · intro j hj
    rw [installMemory, hsecond.2.2.2, hfirst.2.2.2]
    have hout0 : ¬ (address ≤ j ∧ j < address + 4) := by omega
    have hout4 : ¬ (address + 4 ≤ j ∧ j < address + 4 + 4) := by omega
    simp [hout0, hout4]

end WNear.Proofs.InterfaceInstall
