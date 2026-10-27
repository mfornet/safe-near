import Proofs.LoadedCallees
import Binary.ValueReturnLookup
import Proofs.ValueReturnLeaf

/-! The deployed value_return import is the actual resolved metered host,
retained across subsequent code-preserving store updates. -/
namespace WNear.Proofs.LoadedValueReturn
open Wasm Wasm.Near Wasm.Near.MeteredLogic

theorem host (cfg : RuntimeConfig) (original : NearState) (s : Store NearState)
    (mi : ModuleInst) (hload : LoadedCallees.Installed cfg original s mi) :
    mi.funcAddrs[20]? = some 20 ∧
    s.funcs[20]? = some (.host
      (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn) := by
  rcases hload with ⟨loaded, ⟨vm, _, hl⟩, hf, _⟩
  refine ⟨WNear.Binary.ValueReturnLookup.address cfg original vm loaded mi hl, ?_⟩
  rw [hf]
  exact WNear.Binary.ValueReturnLookup.installed cfg original vm loaded mi hl

theorem invoke (cfg : RuntimeConfig) (original : NearState) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (receiver : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (memoryIndex : Nat) (memory : Memory)
    (hload : LoadedCallees.Installed cfg original s mi)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (14 * cfg.wasm.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[260]! [.i32 receiver, .i64 len, .i64 ptr]).map
      (fun c => runInitialized cfg.wasm 4 (.next c)) =
      some (.done [] (ValueReturnLeaf.finalStore cfg.wasm (chargedStore s (11 * cfg.wasm.regularOpCost)) mi len ptr), none) := by
  have hf := LoadedCallees.functions cfg original s mi hload 212
    WNear.Binary.ValueReturnLeaf.function WNear.Binary.ValueReturnLeaf.signature
    WNear.Binary.ValueReturnLeaf.module_function WNear.Binary.ValueReturnLeaf.module_signature
  have hh := host cfg original s mi hload
  have ha : mi.funcAddrs[260]! = 260 := by simp [getElem!_def, hf.1]
  rw [ha]
  exact ValueReturnLeaf.invoke cfg.wasm cfg.fees.numExtraBytesRecord rest s limits 260 0 receiver len ptr
    mi 20 memoryIndex memory hf.2.1 hf.2.2 hh.1 hh.2 hmemoryIndex hmemory hfixed hbound hlimit hc

end WNear.Proofs.LoadedValueReturn
