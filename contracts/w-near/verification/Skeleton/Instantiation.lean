import Skeleton.Module

/-!
# Instantiation facts for the walking skeleton

These are kernel proofs about the actual validator/linker, separate from the
executable scenarios. Memory is kept symbolic wherever possible.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The actual Wasm validator accepts the walking module. -/
theorem module_validates : (module.validate (Features.nearcore true)).isOk = true := by
  decide +kernel

/-- Exactly the four resolved, metered hosts used by `save`. -/
def hosts (cfg : RuntimeConfig) : HostEnv NearState :=
  let extra := cfg.fees.numExtraBytesRecord
  { funcs := [metered extra "input" inputFn,
      metered extra "storage_write" storageWriteFn,
      metered extra "log_utf8" logUtf8Fn,
      metered extra "value_return" valueReturnFn] }

/-- Resolved hosts occupy the first four function slots. -/
theorem hosts_imports (cfg : RuntimeConfig) (host : NearState) :
    ((hosts cfg).allocate (Store.empty host)).2 = [.func 0, .func 1, .func 2, .func 3] := by
  rfl

/-- Their actual metered host signatures satisfy the import declarations. -/
theorem hosts_checkImports (cfg : RuntimeConfig) (host : NearState) :
    Link.checkImports ((hosts cfg).allocate (Store.empty host)).1 module
      (module.imports.toList.zip [.func 0, .func 1, .func 2, .func 3]) = .ok () := by
  rfl

/-- The runtime's resolver selects precisely these hosts for any protocol. -/
theorem resolve_hosts (cfg : RuntimeConfig) : resolveMetered cfg module = .ok (hosts cfg) := by
  rfl

/-- The validated syntax object obtained from the real validator. -/
def validated : ValidModule :=
  match h : module.validate (Features.nearcore true) with
  | .ok v => v
  | .error _ => False.elim (by have hv := module_validates; simp [h, Except.isOk, Except.toBool] at hv)

@[simp] theorem validated_module : validated.module = module := by
  have checked (v : ValidModule) (h : module.validate (Features.nearcore true) = .ok v) :
      v.module = module := by
    unfold Module.validate at h
    cases hc : Validate.module (Features.nearcore true) module with
    | error e => simp [hc] at h
    | ok u => cases u; simp [hc] at h; cases h; rfl
  unfold validated
  split
  · next v h => exact checked v h
  · next e h => have hv := module_validates; simp [h, Except.isOk, Except.toBool] at hv

/-- The module's concrete address spaces after its four hosts are allocated. -/
def moduleInstance : ModuleInst :=
  { types := module.types, funcAddrs := #[0, 1, 2, 3, 4], memAddrs := #[0],
    dataAddrs := #[0], exports := #[("save", .func 4)] }

/-- The store after allocation and data initialization, with memory symbolic. -/
def initializedStore (cfg : RuntimeConfig) (host : NearState) (memory : Memory) : Store NearState :=
  { ((hosts cfg).allocate (Store.empty host)).1 with
    funcs := ((hosts cfg).allocate (Store.empty host)).1.funcs.push
      (.wasm module.types[3]! 0 module.funcs[0]!),
    mems := #[memory], datas := #[{ bytes := ByteArray.empty }], modules := #[moduleInstance] }

/-- Link and initialize the real module. The only memory premise is the
six-byte data write; no large zero-filled byte array is reduced by the kernel. -/
theorem instantiate_module (cfg : RuntimeConfig) (host : NearState) (memory : Memory)
    (hwrite : (Memory.new 1 none).writeBytes 0 module.datas[0]!.init = some memory) :
    Link.instantiateModule ((hosts cfg).allocate (Store.empty host)).1 validated
      [.func 0, .func 1, .func 2, .func 3] = .ok (initializedStore cfg host memory, moduleInstance) := by
  change (Memory.new 1 none).writeBytes 0 ⟨#[107, 115, 97, 118, 101, 100]⟩ = some memory at hwrite
  simp only [Link.instantiateModule, validated_module, hosts_checkImports]
  simp [module, hosts, HostEnv.allocate, Store.empty, Store.allocFunc,
    NearHostFn.toHostFn, Link.importAddrs, Store.allocModule, Link.allocFuncs, Link.allocTables,
    Link.allocMems, Store.allocMem, Link.allocGlobals, Link.allocElems, Link.allocDatas,
    Store.allocData, Link.exportsOf, Store.setModule, Link.initElems, Link.initDatas,
    Link.indexed, Link.initData, Link.evalConst, Exec.i32, Store.memOf, Store.setMemOf,
    initializedStore, moduleInstance, hwrite]

/-- Memory after the data write, retained as a symbolic fold of six writes. -/
def dataMemory (pages : Nat := 1) (max : Option Nat := none) : Memory :=
  (List.range 6).foldl
    (fun memory i => memory.write8 i module.datas[0]!.init[i]!) (Memory.new pages max)

/-- A positive number of pages suffices for the data segment. This proof
uses only the page count and does not reduce any materialized byte page. -/
theorem dataMemory_write (pages : Nat) (max : Option Nat) (hpages : 0 < pages) :
    (Memory.new pages max).writeBytes 0 module.datas[0]!.init = some (dataMemory pages max) := by
  have hb : 0 + module.datas[0]!.init.size ≤ (Memory.new pages max).byteSize := by
    simp only [module, Memory.byteSize, Memory.new, Array.size_replicate]
    change 6 ≤ pages * 65536
    omega
  simp only [Memory.writeBytes, Memory.inBounds, hb, decide_true, ↓reduceIte]
  rfl

/-- Complete initialization from an arbitrary host state. -/
theorem instantiate_dataMemory (cfg : RuntimeConfig) (host : NearState) :
    Link.instantiateModule ((hosts cfg).allocate (Store.empty host)).1 validated
      [.func 0, .func 1, .func 2, .func 3] =
      .ok (initializedStore cfg host (dataMemory 1 none), moduleInstance) :=
  instantiate_module cfg host _ (dataMemory_write 1 none (by decide))

@[simp] theorem initialized_host (cfg : RuntimeConfig) (host : NearState) (memory : Memory) :
    (initializedStore cfg host memory).host = host := rfl

@[simp] theorem initialized_memory (cfg : RuntimeConfig) (host : NearState) (memory : Memory) :
    (initializedStore cfg host memory).memOf moduleInstance = some memory := rfl

@[simp] theorem initialized_export : moduleInstance.export? "save" = some (.func 4) := rfl

@[simp] theorem initialized_function (cfg : RuntimeConfig) (host : NearState) (memory : Memory) :
    (initializedStore cfg host memory).funcs[4]? =
      some (.wasm module.types[3]! 0 module.funcs[0]!) := rfl

end WNear.Skeleton
