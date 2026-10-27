import Proofs.ValueReturnDispatch
import Proofs.LoadedValueReturn
import Wasm.LinkModuleTypes

/-! Deployed host and type lookups for the actual value-return dispatch slice. -/
namespace WNear.Proofs.LoadedValueReturnDispatch
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.ValueReturnDispatch

theorem types (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (mi : ModuleInst) (hload : LoadedCallees.Installed cfg original s mi) :
    mi.types = WNear.Binary.wNearModule.types := by
  rcases hload with ⟨loaded, ⟨vm, hv, hl⟩, _, _⟩
  have h := Link.instantiateModule_types _ vm _ hl
  have hm := WNear.Binary.ImportLayout.validated_module cfg (Features.nearcore true) vm hv
  rw [hm] at h
  exact h

theorem wp_fragment (cfg : RuntimeConfig) (original : NearState) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell slice receiver vtable element : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (tableAddress memoryIndex : Nat)
    (table : TableInst) (memory : Memory) (post : Post)
    (hslice : frame.locals[1]? = some (.i32 slice)) (hsize : 4 ≤ frame.locals.size)
    (hload : LoadedCallees.Installed cfg original s mi) (hinst : frame.inst = 0)
    (htableAddress : mi.tableAddrs[0]? = some tableAddress)
    (htable : s.tables[tableAddress]? = some table)
    (helement : table.elems[element.toNat]? = some (.func 260))
    (hcallerMemoryIndex : mi.memAddrs[0]? = some memoryIndex)
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
    (hc : s.host.gas.Credits (24 * cfg.wasm.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest))
    (hnext : WP cfg.wasm fuel (.next (atCode (fragmentAfter cfg.wasm s mi len ptr) limits base.toArray
      (dispatchFrame frame cell) callers code)) rest post) :
    WP cfg.wasm (fuel + 14) (.next (atCode s limits (base.toArray.push (.i32 cell)) frame callers
      (WNear.Binary.ValueReturnDispatch.dispatch ++ code)))
      (24 * cfg.wasm.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) post := by
  have hf := LoadedCallees.functions cfg original s mi hload 212
    WNear.Binary.ValueReturnLeaf.function WNear.Binary.ValueReturnLeaf.signature
    WNear.Binary.ValueReturnLeaf.module_function WNear.Binary.ValueReturnLeaf.module_signature
  have hh := LoadedValueReturn.host cfg original s mi hload
  have hm : s.modules[frame.inst]? = some mi := by rw [hinst]; exact hf.2.2
  have ht : mi.types[4]? = some WNear.Binary.ValueReturnLeaf.signature := by
    rw [types cfg original s mi hload]
    exact WNear.Binary.ValueReturnLeaf.module_signature
  exact ValueReturnDispatch.wp_fragment cfg.wasm cfg.fees.numExtraBytesRecord fuel rest s limits
    base frame callers code cell slice receiver vtable element len ptr mi mi tableAddress 260 0 20 memoryIndex
    table memory post hslice hsize hm htableAddress htable helement ht hf.2.1 hf.2.2 hh.1 hh.2
    hcallerMemoryIndex hcallerMemoryIndex hmemory hcell hspan hvtable hreceiverRead hvtableRead helementRead
    hlenRead hptrRead hdepth hfixed hbound hlimit hc hnext

end WNear.Proofs.LoadedValueReturnDispatch
