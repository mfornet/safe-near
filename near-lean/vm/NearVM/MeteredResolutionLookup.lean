import NearVM.HostDispatch
import NearVM.HostAllocationLookup

/-! Resolution and allocation preserve the number of imported functions.
The existing `resolveMetered_length` theorem handles a complete module. -/
namespace Wasm.Near

theorem resolveMeteredImports_length (cfg : RuntimeConfig) (decls : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg decls = .ok env) :
    env.funcs.length = decls.length :=
  (resolveMeteredImports_aligned cfg decls env h).length_eq.symm

/-- The loader's function index offset follows from actual successful metered
resolution and actual host allocation, without inspecting the host table. -/
theorem resolveMetered_allocate_importFuncSize (cfg : RuntimeConfig) (m : Module)
    (env : HostEnv NearState) (store : Store NearState)
    (h : resolveMetered cfg m = .ok env) :
    (Link.importAddrs (env.allocate store).2).funcAddrs.size = m.importDecls.length := by
  rw [HostEnv.allocate_importFuncSize, resolveMetered_length cfg m env h]

theorem resolveMetered_allocate_funcSize (cfg : RuntimeConfig) (m : Module)
    (env : HostEnv NearState) (store : Store NearState)
    (h : resolveMetered cfg m = .ok env) :
    (env.allocate store).1.funcs.size = store.funcs.size + m.importDecls.length := by
  rw [HostEnv.allocate_funcSize, resolveMetered_length cfg m env h]

end Wasm.Near
