import Proofs.LoadedValueReturnDispatch
import Binary.ValueReturnLayout
import Wasm.LinkTableLookup

/-! The actual return-vtable target follows from successful loading. Later guest
code may update tables, so dispatch uses a load invariant that retains tables
alongside the existing function/module fields. -/
namespace WNear.Proofs.LoadedValueReturnTable
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.ValueReturnDispatch

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

/-- The active element segment installs f260 at table slot58. This follows
from the actual successful linker, without a table-address or content premise. -/
theorem loaded_lookup (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (hload : LoadedCallees.Loaded cfg original s inst) :
    ∃ address table, inst.tableAddrs[0]? = some address ∧
      s.tables[address]? = some table ∧ table.elems[58]? = some (.func 260) := by
  have hfunction := LoadedCallees.functions cfg original s inst
    (LoadedCallees.loaded_installed cfg original s inst hload) 212
    WNear.Binary.ValueReturnLeaf.function WNear.Binary.ValueReturnLeaf.signature
    WNear.Binary.ValueReturnLeaf.module_function WNear.Binary.ValueReturnLeaf.module_signature
  rcases hload with ⟨vm, hv, hl⟩
  have hm := WNear.Binary.ImportLayout.validated_module cfg (Features.nearcore true) vm hv
  have he : vm.module.elems = #[element] := by
    rw [hm]
    exact element_singleton
  have hmode : element.mode = .active 0 [.i32_const 1] :=
    WNear.Binary.ValueReturnLayout.element_offset
  have hc : element.init[57]? = some [.ref_func 260] :=
    WNear.Binary.ValueReturnLayout.return_element
  have hf : inst.funcAddrs[260]? = some 260 := hfunction.1
  exact Link.instantiateModule_single_active_ref _ vm _ s inst hl element he
    0 57 260 260 1 hmode hc hf

/-- Retain actual loaded tables in addition to installed code. Equality of
these store fields is preserved by the already-proved memory/host slices. -/
def Installed (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) : Prop :=
  ∃ loaded, LoadedCallees.Loaded cfg original loaded inst ∧
    s.funcs = loaded.funcs ∧ s.modules = loaded.modules ∧ s.tables = loaded.tables

theorem loaded_installed (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (h : LoadedCallees.Loaded cfg original s inst) :
    Installed cfg original s inst := ⟨s, h, rfl, rfl, rfl⟩

theorem installed_code (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (h : Installed cfg original s inst) :
    LoadedCallees.Installed cfg original s inst := by
  rcases h with ⟨loaded, hl, hf, hm, _⟩
  exact ⟨loaded, hl, hf, hm⟩

theorem installed_frame (cfg : RuntimeConfig) (original : NearState) (s t : Store NearState)
    (inst : ModuleInst) (h : Installed cfg original s inst)
    (hf : t.funcs = s.funcs) (hm : t.modules = s.modules) (ht : t.tables = s.tables) :
    Installed cfg original t inst := by
  rcases h with ⟨loaded, hl, hfs, hms, hts⟩
  exact ⟨loaded, hl, hf.trans hfs, hm.trans hms, ht.trans hts⟩

theorem installed_lookup (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (inst : ModuleInst) (h : Installed cfg original s inst) :
    ∃ address table, inst.tableAddrs[0]? = some address ∧
      s.tables[address]? = some table ∧ table.elems[58]? = some (.func 260) := by
  rcases h with ⟨loaded, hl, _, _, ht⟩
  rw [ht]
  exact loaded_lookup cfg original loaded inst hl

/-- Dispatch uses the table selected by actual initialization. Individual
address, descriptor and function-reference lookup premises are discharged. -/
theorem wp_fragment (cfg : RuntimeConfig) (original : NearState) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell slice receiver vtable : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (memoryIndex : Nat)
    (memory : Memory) (post : Post)
    (hslice : frame.locals[1]? = some (.i32 slice)) (hsize : 4 ≤ frame.locals.size)
    (hload : Installed cfg original s mi) (hinst : frame.inst = 0)
    (hcallerMemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hcell : cell.toNat + 8 ≤ memory.byteSize) (hspan : slice.toNat + 8 ≤ memory.byteSize)
    (hvtable : vtable.toNat + 96 ≤ memory.byteSize)
    (hreceiverRead : readI32 memory cell.toNat = receiver)
    (hvtableRead : readI32 memory (cell.toNat + 4) = vtable)
    (helementRead : readI32 memory (vtable.toNat + 92) = 58)
    (hlenRead : packed32 memory (slice.toNat + 4) = len) (hptrRead : packed32 memory slice.toNat = ptr)
    (hdepth : callers.length + 1 < limits.maxCallDepth)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (24 * cfg.wasm.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest))
    (hnext : WP cfg.wasm fuel (.next (atCode (fragmentAfter cfg.wasm s mi len ptr) limits base.toArray
      (dispatchFrame frame cell) callers code)) rest post) :
    WP cfg.wasm (fuel + 14) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers
      (WNear.Binary.ValueReturnDispatch.dispatch ++ code)))
      (24 * cfg.wasm.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) post := by
  rcases installed_lookup cfg original s mi hload with ⟨tableAddress, table, ha, ht, he⟩
  exact LoadedValueReturnDispatch.wp_fragment cfg original fuel rest s limits base frame callers
    code cell slice receiver vtable 58 len ptr mi tableAddress memoryIndex table memory post
    hslice hsize (installed_code cfg original s mi hload) hinst ha ht he
    hcallerMemoryIndex hmemory hcell hspan hvtable hreceiverRead hvtableRead helementRead
    hlenRead hptrRead hdepth hfixed hbound hlimit hc hnext

end WNear.Proofs.LoadedValueReturnTable
