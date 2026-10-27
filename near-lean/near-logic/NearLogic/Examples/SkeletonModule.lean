import NearLogic.Examples.Skeleton
import NearLogic.Instantiate
import NearVM.Fuel
import WasmLogic.Tactic

/-!
# The walking skeleton's module

The module of `Examples/Skeleton.lean` as a term, and what `runAttempt` does
with it before the method runs.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near

def skelModule : Module where
  types := #[{ params := [], results := [] }, { params := [.i64, .i64], results := [] }]
  imports := #[{ «module» := "env", name := "value_return", desc := .func 1 }]
  funcs := #[{ type := 0, locals := [], body := body }]
  mems := #[{ type := { limits := { min := 1, max := none } } }]
  datas := #[{ init := ⟨okBytes.toArray⟩, mode := .active 0 [.i32_const 0] }]
  exports := #[{ name := "get", desc := .func 1 }, { name := "memory", desc := .mem 0 }]

/-- The metered `value_return` the module is linked with. -/
theorem resolve_skel (cfg : RuntimeConfig) :
    resolveMetered cfg (prepareMemory cfg skelModule) =
      .ok { funcs := [metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn] } := by
  rfl

/-- The module as nearcore prepares it under the v86 memory limits. -/
def skelPrepared : Module :=
  { skelModule with mems := #[{ type := { limits := { min := 1024, max := some 2048 } } }] }

theorem prepare_skel (cfg : RuntimeConfig) (hmin : cfg.wasm.limits.initialMemoryPages = 1024)
    (hmax : cfg.wasm.limits.maxMemoryPages = 2048) : prepareMemory cfg skelModule = skelPrepared := by
  simp [prepareMemory, skelModule, skelPrepared, hmin, hmax]

theorem validate_skel_ok : (match skelPrepared.validate (Features.nearcore true) with
    | .ok _ => true | .error _ => false) = true := by kernel_rfl

theorem validate_skel : ∃ vm, skelPrepared.validate (Features.nearcore true) = .ok vm ∧
    vm.module = skelPrepared := by
  have hok := validate_skel_ok
  revert hok
  cases h : skelPrepared.validate (Features.nearcore true) with
  | ok vm => intro _; exact ⟨vm, rfl, Wasm.Near.validate_module h⟩
  | error e => intro hok; cases hok

/-- The instance of the module. -/
def instSkel : ModuleInst :=
  { types := skelModule.types, funcAddrs := #[0, 1], memAddrs := #[0], dataAddrs := #[0],
    exports := #[("get", .func 1), ("memory", .mem 0)] }

/-- The memory after the data segment. -/
def dataMem : Memory := ((Memory.new 1024 (some 2048)).writeBytes 0 ⟨okBytes.toArray⟩).get!

/-- The instantiated store, from the host `h`. -/
def storeSkel (extra : Nat) (h : NearState) : Store NearState :=
  { funcs := #[.host (metered extra "value_return" valueReturnFn).toHostFn,
      .wasm skelModule.types[0]! 0 skelModule.funcs[0]!],
    mems := #[dataMem], datas := #[{ bytes := .empty }], modules := #[instSkel], host := h }

set_option maxRecDepth 200000 in
theorem instantiate_skel (extra : Nat) (h : NearState) (vm : ValidModule) (hvm : vm.module = skelPrepared) :
    Link.instantiateModule
      ({ funcs := #[.host (metered extra "value_return" valueReturnFn).toHostFn], host := h } : Store NearState)
      vm [.func 0] = .ok (storeSkel extra h, instSkel) := by
  obtain ⟨m', hw, -⟩ := writeBytes_spec (Memory.new_wf 1024 (some 2048)) (addr := 0)
    (bytes := ⟨okBytes.toArray⟩) (by simp [Memory.new_byteSize, okBytes, pageSize, ByteArray.size])
  have hd : dataMem = m' := by simp [dataMem, hw]
  have ht : (metered extra "value_return" valueReturnFn).toHostFn.type =
      { params := [.i64, .i64], results := [] } := rfl
  unfold Link.instantiateModule
  rw [hvm]
  simp [skelPrepared, skelModule, Link.checkImports, Link.checkImport, Link.importAddrs, Store.allocModule,
    Link.allocFuncs, Store.allocFunc, Link.allocTables, Link.allocMems, Store.allocMem, Link.allocGlobals,
    Link.allocElems, Link.allocDatas, Store.allocData, Link.exportsOf, Store.setModule, Link.initElems,
    Link.indexed, Link.initDatas, Link.initData, Link.evalConst, Store.memOf, Store.setMemOf,
    FuncInst.type, ht, Exec.i32, hw, storeSkel, instSkel, hd]
  done

end NearLogic.Skeleton
