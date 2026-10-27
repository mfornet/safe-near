import Proofs.LoadedValueReturnTable
import Proofs.ValueReturnThreadLocal
import Binary.ValueReturnLookupLayout

/-! Loading derives the interface lookup table entry, rather than assuming
its address/content at the initialized f456 lookup. -/
namespace WNear.Proofs.LoadedValueReturnLookup
open Wasm Wasm.Near MeteredLogic

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

/-- The active element segment installs f565 at table slot116. This follows
from the actual successful linker, without a table-address or content premise. -/
theorem loaded_lookup (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (hload : LoadedCallees.Loaded cfg original s inst) :
    ∃ address table, inst.tableAddrs[0]? = some address ∧
      s.tables[address]? = some table ∧ table.elems[116]? = some (.func 565) := by
  have hfunction := LoadedCallees.functions cfg original s inst
    (LoadedCallees.loaded_installed cfg original s inst hload) 517
    WNear.Binary.ValueReturnThreadLocal.lookupFunction WNear.Binary.ValueReturnThreadLocal.lookupSignature
    WNear.Binary.ValueReturnThreadLocal.lookup_function WNear.Binary.ValueReturnThreadLocal.lookup_signature
  rcases hload with ⟨vm, hv, hl⟩
  have hm := WNear.Binary.ImportLayout.validated_module cfg (Features.nearcore true) vm hv
  have he : vm.module.elems = #[element] := by
    rw [hm]
    exact element_singleton
  have hmode : element.mode = .active 0 [.i32_const 1] :=
    WNear.Binary.ValueReturnLayout.element_offset
  have hc : element.init[115]? = some [.ref_func 565] :=
    WNear.Binary.ValueReturnLookupLayout.lookup_element
  have hf : inst.funcAddrs[565]? = some 565 := hfunction.1
  exact Link.instantiateModule_single_active_ref _ vm _ s inst hl element he
    0 115 565 565 1 hmode hc hf

theorem installed_lookup (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (h : LoadedValueReturnTable.Installed cfg original s inst) :
    ∃ address table, inst.tableAddrs[0]? = some address ∧
      s.tables[address]? = some table ∧ table.elems[116]? = some (.func 565) := by
  rcases h with ⟨loaded, hl, _, _, ht⟩
  rw [ht]
  exact loaded_lookup cfg original loaded inst hl

theorem wp_indirect_lookup (cfg : RuntimeConfig) (original : NearState) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hload : LoadedValueReturnTable.Installed cfg original s mi) (hinst : frame.inst = 0)
    (hindex : mi.memAddrs[0]? = some index) (hmemory : s.mems[index]? = some memory)
    (hbound : 1074900 + 4 ≤ memory.byteSize) (hstatus : readI32 memory 1074900 = 1)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (29 * cfg.wasm.regularOpCost + rest))
    (hnext : WP cfg.wasm fuel (.next (atCode (ValueReturnThreadLocal.indirectAfter s cfg.wasm.regularOpCost) limits
      (base ++ [Value.i32 1074904]).toArray frame callers code)) rest post) :
    WP cfg.wasm (fuel + 15) (.next (atCode s limits (base.toArray.push (.i32 116)) frame callers
      (.call_indirect 1 0 :: code))) (29 * cfg.wasm.regularOpCost + rest) post := by
  have hcode := LoadedValueReturnTable.installed_code cfg original s mi hload
  obtain ⟨tableAddress, table, hta, ht, he⟩ := installed_lookup cfg original s mi hload
  have lookup := LoadedCallees.functions cfg original s mi hcode 517
    WNear.Binary.ValueReturnThreadLocal.lookupFunction WNear.Binary.ValueReturnThreadLocal.lookupSignature
    WNear.Binary.ValueReturnThreadLocal.lookup_function WNear.Binary.ValueReturnThreadLocal.lookup_signature
  have helper := LoadedCallees.functions cfg original s mi hcode 420
    WNear.Binary.ValueReturnThreadLocal.function WNear.Binary.ValueReturnThreadLocal.signature
    WNear.Binary.ValueReturnThreadLocal.module_function WNear.Binary.ValueReturnThreadLocal.module_signature
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact lookup.2.2
  have hf : s.funcs[565]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst
      WNear.Binary.ValueReturnThreadLocal.lookupFunction) := by rw [hinst]; exact lookup.2.1
  have hh : s.funcs[468]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst
      WNear.Binary.ValueReturnThreadLocal.function) := by rw [hinst]; exact helper.2.1
  have htype : mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature := by
    rw [LoadedValueReturnDispatch.types cfg original s mi hcode]
    exact WNear.Binary.ValueReturnThreadLocal.lookup_signature
  exact ValueReturnThreadLocal.wp_indirect_lookup cfg.wasm fuel rest s limits base frame callers code mi
    tableAddress 565 468 index 116 table memory post hm hta ht he htype hf helper.1 hh hindex hmemory
    hbound hstatus hdepth hc hnext

end WNear.Proofs.LoadedValueReturnLookup
