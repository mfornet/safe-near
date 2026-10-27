import Binary.ImportLayout
import Wasm.LinkFunctionLookup

/-! Actual resolved host implementation of the deployed value_return import. -/
namespace WNear.Binary.ValueReturnLookup
open Wasm Wasm.Near

theorem resolved (cfg : RuntimeConfig) :
    (ImportLayout.hosts cfg).funcs[20]? =
      some (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn) := by
  rfl

/-- Data/element initialization preserves the allocated host-function prefix. -/
theorem installed (cfg : RuntimeConfig) (host : NearState) (vm : ValidModule)
    (after : Store NearState) (inst : ModuleInst)
    (hlink : Link.instantiateModule ((ImportLayout.hosts cfg).allocate (Store.empty host)).1 vm
      ((ImportLayout.hosts cfg).allocate (Store.empty host)).2 = .ok (after, inst)) :
    after.funcs[20]? = some (.host
      (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn) := by
  have hl := Link.instantiateModule_arrays _ vm _ hlink
  have hs : ((ImportLayout.hosts cfg).allocate (Store.empty host)).1.funcs.size = 48 := by
    simpa only [HostEnv.allocate_funcSize, Store.empty, Array.size_empty, Nat.zero_add] using ImportLayout.hosts_length cfg
  rw [hl.1, Array.getElem?_append_left (by omega : 20 < ((ImportLayout.hosts cfg).allocate (Store.empty host)).1.funcs.size)]
  rw [HostEnv.allocate_funcArray]
  simp only [Store.empty, Array.empty_append]
  simp only [List.getElem?_toArray, List.getElem?_map, resolved, Option.map_some]

theorem address (cfg : RuntimeConfig) (host : NearState) (vm : ValidModule)
    (after : Store NearState) (inst : ModuleInst)
    (hlink : Link.instantiateModule ((ImportLayout.hosts cfg).allocate (Store.empty host)).1 vm
      ((ImportLayout.hosts cfg).allocate (Store.empty host)).2 = .ok (after, inst)) :
    inst.funcAddrs[20]? = some 20 := by
  have hl := Link.instantiateModule_arrays _ vm _ hlink
  have hs : (Link.importAddrs ((ImportLayout.hosts cfg).allocate (Store.empty host)).2).funcAddrs.size = 48 := by
    rw [HostEnv.allocate_importFuncSize, ImportLayout.hosts_length]
  rw [hl.2.1, Array.getElem?_append_left (by omega : 20 < (Link.importAddrs ((ImportLayout.hosts cfg).allocate (Store.empty host)).2).funcAddrs.size)]
  rw [HostEnv.allocate_imports]
  simp only [Store.empty, Array.size_empty, ImportLayout.hosts_length]
  rfl

end WNear.Binary.ValueReturnLookup
