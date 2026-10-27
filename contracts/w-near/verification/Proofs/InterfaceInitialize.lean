import Binary.InterfaceInitialize
import Proofs.StorePairCaller
import NearVM.MeteredIndirectCall
import Proofs.LoadedValueReturnTable
import Proofs.LoadedValueReturnData

/-! Actual indirect initializer of the lazy interface cell. It zeroes exactly
eight bytes; the following scratch word is deliberately preserved, not zeroed. -/
namespace WNear.Proofs.InterfaceInitialize
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

def bodyAfter (s : Store NearState) (op index address : Nat) (memory : Memory) : Store NearState :=
  storeI64 (paid s op 3) index address memory 0

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hlocal : frame.locals[0]? = some (.i32 pointer))
    (hmodule : s.modules[frame.inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hbound : pointer.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyAfter s cfg.regularOpCost index pointer.toNat memory)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers (WNear.Binary.InterfaceInitialize.body ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 pointer) post hlocal (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i64_const cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    {align := 2, offset := 0} pointer 0 mi index memory post
  · exact hmodule
  · exact hindex
  · exact hmemory
  · simpa using hbound
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

def entry (s : Store NearState) (op : Nat) : Store NearState := chargedStore (chargedStore s op) (9 * op)
def after (s : Store NearState) (op index address : Nat) (memory : Memory) : Store NearState :=
  bodyAfter (entry s op) op index address memory

/-- Full actual type0 indirect call to f564, including activation and void
return. There is no initializer execution hypothesis or continuation in its body. -/
theorem wp_indirect (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst)
    (tableAddress address index : Nat) (element : UInt32) (table : TableInst) (memory : Memory) (post : Post)
    (hmodule : s.modules[frame.inst]? = some mi) (htableAddress : mi.tableAddrs[0]? = some tableAddress)
    (htable : s.tables[tableAddress]? = some table) (helement : table.elems[element.toNat]? = some (.func address))
    (htype : mi.types[0]? = some WNear.Binary.InterfaceInitialize.signature)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst
      WNear.Binary.InterfaceInitialize.function))
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : pointer.toNat + 8 ≤ memory.byteSize) (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index pointer.toNat memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits ((base ++ [Value.i32 pointer]).toArray.push (.i32 element)) frame callers
      (.call_indirect 0 0 :: code))) (13 * cfg.regularOpCost + rest) post := by
  let active := entry s cfg.regularOpCost
  let leaf : CallFrame := {locals := #[Value.i32 pointer], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code := code}
  have h0 : s.host.gas.Credits (cfg.regularOpCost + (9 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s cfg.regularOpCost _ h0
  have h2 : active.host.gas.Credits (3 * cfg.regularOpCost + rest) :=
    WNear.Proofs.StorePair.charged_credits (chargedStore s cfg.regularOpCost) (9 * cfg.regularOpCost) _ h1
  have hf : (after s cfg.regularOpCost index pointer.toNat memory).host.gas.Credits rest :=
    paid_credits active cfg.regularOpCost 3 rest h2
  have hn : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index pointer.toNat memory) limits
      (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [List.append_nil, saved, atCode] using hnext
  have leave := wp_leave_wasm cfg fuel rest (after s cfg.regularOpCost index pointer.toNat memory) limits base []
    leaf saved callers post rfl rfl rfl hf hn
  have next : WP cfg (fuel + 1) (.next (atCode (bodyAfter active cfg.regularOpCost index pointer.toNat memory) limits
      base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [List.append_nil, after, active] using leave
  have hm : active.modules[leaf.inst]? = some mi := hmodule
  have hmem : active.mems[index]? = some memory := hmemory
  have body := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) []
    pointer mi index memory post rfl hm hindex hmem hbound h2 next
  have activation : activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.InterfaceInitialize.function [Value.i32 pointer]) = 9 * cfg.regularOpCost := by
    simp [activationGas, wasmLocals, WNear.Binary.InterfaceInitialize.function]
  have rule := wp_call_indirect_wasm cfg ((fuel + 1) + 3) (3 * cfg.regularOpCost + rest) s limits base
    [Value.i32 pointer] frame callers code 0 0 tableAddress address element table mi WNear.Binary.InterfaceInitialize.signature
    frame.inst WNear.Binary.InterfaceInitialize.function post hmodule htableAddress htable helement htype hfunction rfl hdepth
  rw [activation] at rule
  have nextBody : WP cfg ((fuel + 1) + 3) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.InterfaceInitialize.signature frame.inst WNear.Binary.InterfaceInitialize.function [Value.i32 pointer]))
      (3 * cfg.regularOpCost + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.InterfaceInitialize.function,
      WNear.Binary.InterfaceInitialize.signature, WNear.Binary.InterfaceInitialize.body, atCode, leaf, saved,
      List.map_nil, List.append_nil, Array.append_empty, List.length_cons, List.length_nil] using body
  have result := rule h0 nextBody
  rw [show cfg.regularOpCost + (9 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest)) =
      13 * cfg.regularOpCost + rest by omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

theorem after_credits (s : Store NearState) (op index address rest : Nat) (memory : Memory)
    (hc : s.host.gas.Credits (13 * op + rest)) : (after s op index address memory).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (op + (9 * op + (3 * op + rest))) := hc.mono (by omega)
  have h1 := WNear.Proofs.StorePair.charged_credits s op _ h0
  have h2 := WNear.Proofs.StorePair.charged_credits (chargedStore s op) (9 * op) _ h1
  exact paid_credits (entry s op) op 3 rest h2

/-- Exactly eight bytes are written, with every other memory byte retained. -/
theorem memory_spec (memory : Memory) (address : Nat) (hwf : memory.wf)
    (hbound : address + 8 ≤ memory.byteSize) :
    (writeI64 memory address 0).wf ∧ (writeI64 memory address 0).byteSize = memory.byteSize ∧
    (writeI64 memory address 0).max = memory.max ∧
    ∀ j, (writeI64 memory address 0).read8 j =
      if address ≤ j ∧ j < address + 8 then 0 else memory.read8 j := by
  have hz : UInt8.ofNat 0 = (0 : UInt8) := rfl
  simpa only [UInt64.toNat_zero, Nat.zero_shiftRight, hz] using
    writeI64_spec memory address 0 hwf hbound

theorem after_memory (s : Store NearState) (op index address : Nat) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (after s op index address memory).mems[index]? = some (writeI64 memory address 0) := by
  have hp : (paid (entry s op) op 3).mems[index]? = some memory := by
    simpa only [entry, paid, chargedStore] using hm
  have hh := storeI64_memory (paid (entry s op) op 3) index address memory 0 hp
  simpa only [after, bodyAfter] using hh

theorem after_resources (s : Store NearState) (op index address : Nat) (memory : Memory) :
    {after s op index address memory with mems := s.mems, host := s.host} = s := by
  simp only [after, bodyAfter, entry, paid, chargedStore, storeI64]

/-- The initialized i64 word is exactly zero. -/
theorem zero_word (memory : Memory) (address : Nat) (hwf : memory.wf)
    (hbound : address + 8 ≤ memory.byteSize) :
    readI64 (writeI64 memory address 0) address = 0 := by
  have hs := memory_spec memory address hwf hbound
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [hs.2.2.2]
  have hin : address ≤ address + i ∧ address + i < address + 8 := by omega
  simp [hin]

/-- The additional four bytes read by f467 are retained from the incoming
scratch memory, rather than being initialized to zero. -/
theorem following_word (memory : Memory) (address : Nat) (hwf : memory.wf)
    (hbound : address + 8 ≤ memory.byteSize) :
    readI32 (writeI64 memory address 0) (address + 8) = readI32 memory (address + 8) := by
  have hs := memory_spec memory address hwf hbound
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  rw [hs.2.2.2]
  have hout : ¬ (address ≤ address + 8 + i ∧ address + 8 + i < address + 8) := by omega
  rw [ite_eq_right hout]

private noncomputable def element : Elem := WNear.Binary.wNearModule.elems[0]!

private theorem element_singleton : WNear.Binary.wNearModule.elems = #[element] := by
  apply Array.ext
  · simpa only [Array.size_singleton] using WNear.Binary.ValueReturnLayout.element_count
  · intro i hi hj
    have h0 : i = 0 := by
      have hs := WNear.Binary.ValueReturnLayout.element_count
      omega
    subst i
    change WNear.Binary.wNearModule.elems[0] = WNear.Binary.wNearModule.elems[0]!
    exact (getElem!_pos WNear.Binary.wNearModule.elems 0 hi).symm

/-- The actual linker installs the proven initializer at table index106. -/
theorem loaded_table (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (mi : ModuleInst) (hload : LoadedCallees.Loaded cfg original s mi) :
    ∃ address table, mi.tableAddrs[0]? = some address ∧ s.tables[address]? = some table ∧
      table.elems[106]? = some (.func 564) := by
  have hf := LoadedCallees.functions cfg original s mi
    (LoadedCallees.loaded_installed cfg original s mi hload) 516
    WNear.Binary.InterfaceInitialize.function WNear.Binary.InterfaceInitialize.signature
    WNear.Binary.InterfaceInitialize.module_function WNear.Binary.InterfaceInitialize.module_signature
  rcases hload with ⟨vm, hv, hl⟩
  have hm := WNear.Binary.ImportLayout.validated_module cfg (Features.nearcore true) vm hv
  have he : vm.module.elems = #[element] := by rw [hm]; exact element_singleton
  have hmode : element.mode = .active 0 [.i32_const 1] := WNear.Binary.ValueReturnLayout.element_offset
  have hc : element.init[105]? = some [.ref_func 564] := WNear.Binary.InterfaceInitialize.table_element
  exact Link.instantiateModule_single_active_ref _ vm _ s mi hl element he
    0 105 564 564 1 hmode hc hf.1

theorem installed_table (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (mi : ModuleInst) (hload : LoadedValueReturnTable.Installed cfg original s mi) :
    ∃ address table, mi.tableAddrs[0]? = some address ∧ s.tables[address]? = some table ∧
      table.elems[106]? = some (.func 564) := by
  rcases hload with ⟨loaded, hl, _, _, ht⟩
  rw [ht]
  exact loaded_table cfg original loaded mi hl

/-- An actual loaded module supplies all table/type/function descriptors for
this call; only current memory resolution, writable span and depth remain. -/
theorem wp_installed (cfg : RuntimeConfig) (original : NearState) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hload : LoadedValueReturnTable.Installed cfg original s mi) (hinst : frame.inst = 0)
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : pointer.toNat + 8 ≤ memory.byteSize) (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (13 * cfg.wasm.regularOpCost + rest))
    (hnext : WP cfg.wasm fuel (.next (atCode (after s cfg.wasm.regularOpCost index pointer.toNat memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg.wasm (fuel + 5) (.next (atCode s limits ((base ++ [Value.i32 pointer]).toArray.push (.i32 106)) frame callers
      (.call_indirect 0 0 :: code))) (13 * cfg.wasm.regularOpCost + rest) post := by
  have hcode := LoadedValueReturnTable.installed_code cfg original s mi hload
  have hf := LoadedCallees.functions cfg original s mi hcode 516
    WNear.Binary.InterfaceInitialize.function WNear.Binary.InterfaceInitialize.signature
    WNear.Binary.InterfaceInitialize.module_function WNear.Binary.InterfaceInitialize.module_signature
  obtain ⟨address, table, ha, ht, he⟩ := installed_table cfg original s mi hload
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact hf.2.2
  have hfunction : s.funcs[564]? = some (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst
      WNear.Binary.InterfaceInitialize.function) := by rw [hinst]; exact hf.2.1
  have htype : mi.types[0]? = some WNear.Binary.InterfaceInitialize.signature := by
    rw [LoadedValueReturnDispatch.types cfg original s mi hcode]
    exact WNear.Binary.InterfaceInitialize.module_signature
  exact wp_indirect cfg.wasm fuel rest s limits base frame callers code pointer mi address 564 index 106
    table memory post hm ha ht he htype hfunction hindex hmemory hbound hdepth hc hnext

end WNear.Proofs.InterfaceInitialize
