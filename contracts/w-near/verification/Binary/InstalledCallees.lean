import Binary.StorePair
import Binary.StorePairCaller
import Binary.PackWords
import Binary.ExpectResult
import Wasm.LinkFunctionLookup
import Binary.ImportLayout

/-! Function-table facts for successful loading of the prepared deployed module.
Memory initialization remains symbolic; no data payload is evaluated. -/
namespace WNear.Binary.InstalledCallees
open Wasm Wasm.Near

/-- Preparation changes the memory declaration, retaining the actual function
and type tables. The import count describes the function address space. -/
theorem defined_lookup (cfg : RuntimeConfig) (before : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (hmodule : vm.module = prepareMemory cfg wNearModule)
    (hlink : Link.instantiateModule before vm imports = .ok (after, inst))
    (hcount : (Link.importAddrs imports).funcAddrs.size = 48)
    (n : Nat) (function : Func) (signature : FuncType)
    (hfunction : wNearModule.funcs[n]? = some function)
    (htype : wNearModule.types[function.type]? = some signature) :
    inst.funcAddrs[48 + n]? = some (before.funcs.size + n) ∧
    after.funcs[before.funcs.size + n]? =
      some (.wasm signature before.modules.size function) ∧
    after.modules[before.modules.size]? = some inst := by
  have hf : vm.module.funcs[n]? = some function := by
    simpa only [hmodule, prepareMemory] using hfunction
  have ht : vm.module.types[function.type]? = some signature := by
    simpa only [hmodule, prepareMemory] using htype
  have h := Link.instantiateModule_defined before vm imports hlink n function signature hf ht
  simpa only [hcount] using h

theorem storePair (cfg : RuntimeConfig) (before : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (hmodule : vm.module = prepareMemory cfg wNearModule)
    (hlink : Link.instantiateModule before vm imports = .ok (after, inst))
    (hcount : (Link.importAddrs imports).funcAddrs.size = 48) :
    inst.funcAddrs[566]? = some (before.funcs.size + 518) ∧
    after.funcs[before.funcs.size + 518]? =
      some (.wasm StorePair.signature before.modules.size StorePair.function) ∧
    after.modules[before.modules.size]? = some inst :=
  defined_lookup cfg before vm imports after inst hmodule hlink hcount 518
    StorePair.function StorePair.signature StorePair.module_function StorePair.module_signature

theorem storePairCaller (cfg : RuntimeConfig) (before : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (hmodule : vm.module = prepareMemory cfg wNearModule)
    (hlink : Link.instantiateModule before vm imports = .ok (after, inst))
    (hcount : (Link.importAddrs imports).funcAddrs.size = 48) :
    inst.funcAddrs[414]? = some (before.funcs.size + 366) ∧
    after.funcs[before.funcs.size + 366]? =
      some (.wasm StorePairCaller.signature before.modules.size StorePairCaller.function) ∧
    after.modules[before.modules.size]? = some inst :=
  defined_lookup cfg before vm imports after inst hmodule hlink hcount 366
    StorePairCaller.function StorePairCaller.signature
    StorePairCaller.module_function StorePairCaller.module_signature

theorem packWords (cfg : RuntimeConfig) (before : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (hmodule : vm.module = prepareMemory cfg wNearModule)
    (hlink : Link.instantiateModule before vm imports = .ok (after, inst))
    (hcount : (Link.importAddrs imports).funcAddrs.size = 48) :
    inst.funcAddrs[779]? = some (before.funcs.size + 731) ∧
    after.funcs[before.funcs.size + 731]? =
      some (.wasm PackWords.signature before.modules.size PackWords.function) ∧
    after.modules[before.modules.size]? = some inst :=
  defined_lookup cfg before vm imports after inst hmodule hlink hcount 731
    PackWords.function PackWords.signature PackWords.module_function PackWords.module_signature

theorem expectResult (cfg : RuntimeConfig) (before : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (hmodule : vm.module = prepareMemory cfg wNearModule)
    (hlink : Link.instantiateModule before vm imports = .ok (after, inst))
    (hcount : (Link.importAddrs imports).funcAddrs.size = 48) :
    inst.funcAddrs[158]? = some (before.funcs.size + 110) ∧
    after.funcs[before.funcs.size + 110]? =
      some (.wasm ExpectResult.signature before.modules.size ExpectResult.function) ∧
    after.modules[before.modules.size]? = some inst :=
  defined_lookup cfg before vm imports after inst hmodule hlink hcount 110
    ExpectResult.function ExpectResult.signature ExpectResult.module_function ExpectResult.module_signature

/-- Follow the actual runtime pipeline: validate the prepared deployed code,
resolve its hosts, allocate them and link. Function offsets and module slots
are conclusions, rather than caller-supplied lookup premises. -/
theorem actual_defined_lookup (cfg : RuntimeConfig) (before : Store NearState)
    (vm : ValidModule) (after : Store NearState) (inst : ModuleInst)
    (hvalidate : (prepareMemory cfg wNearModule).validate (Features.nearcore true) = .ok vm)
    (hlink : Link.instantiateModule ((ImportLayout.hosts cfg).allocate before).1 vm
      ((ImportLayout.hosts cfg).allocate before).2 = .ok (after, inst))
    (n : Nat) (function : Func) (signature : FuncType)
    (hfunction : wNearModule.funcs[n]? = some function)
    (htype : wNearModule.types[function.type]? = some signature) :
    inst.funcAddrs[48 + n]? = some (before.funcs.size + (48 + n)) ∧
    after.funcs[before.funcs.size + (48 + n)]? =
      some (.wasm signature before.modules.size function) ∧
    after.modules[before.modules.size]? = some inst := by
  have hm := ImportLayout.validated_module cfg (Features.nearcore true) vm hvalidate
  have hc : (Link.importAddrs ((ImportLayout.hosts cfg).allocate before).2).funcAddrs.size = 48 := by
    rw [HostEnv.allocate_importFuncSize, ImportLayout.hosts_length]
  have hs : ((ImportLayout.hosts cfg).allocate before).1.funcs.size = before.funcs.size + 48 := by
    rw [HostEnv.allocate_funcSize, ImportLayout.hosts_length]
  have hmods := HostEnv.allocate_modules before (ImportLayout.hosts cfg)
  have h := defined_lookup cfg ((ImportLayout.hosts cfg).allocate before).1 vm
    ((ImportLayout.hosts cfg).allocate before).2 after inst hm hlink hc n function signature hfunction htype
  simpa only [hs, hmods, Nat.add_assoc] using h

/-- The runtime starts host allocation from an empty store. Consequently the
deployed global function indices are their actual installed addresses. -/
theorem from_empty (cfg : RuntimeConfig) (host : NearState) (vm : ValidModule)
    (after : Store NearState) (inst : ModuleInst)
    (hvalidate : (prepareMemory cfg wNearModule).validate (Features.nearcore true) = .ok vm)
    (hlink : Link.instantiateModule ((ImportLayout.hosts cfg).allocate (Store.empty host)).1 vm
      ((ImportLayout.hosts cfg).allocate (Store.empty host)).2 = .ok (after, inst))
    (n : Nat) (function : Func) (signature : FuncType)
    (hfunction : wNearModule.funcs[n]? = some function)
    (htype : wNearModule.types[function.type]? = some signature) :
    inst.funcAddrs[48 + n]? = some (48 + n) ∧
    after.funcs[48 + n]? = some (.wasm signature 0 function) ∧
    after.modules[0]? = some inst := by
  have h := actual_defined_lookup cfg (Store.empty host) vm after inst hvalidate hlink
    n function signature hfunction htype
  simpa only [Store.empty, Array.size_empty, Nat.zero_add] using h

end WNear.Binary.InstalledCallees
