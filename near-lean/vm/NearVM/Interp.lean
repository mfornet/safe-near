import Wasm.Link
import Wasm.Bytes

/-!
# The NEAR host functions' view of the runtime

NEAR host functions are written against `HostStore`: the contract's linear
memory and the host state, nothing else. `NearHostFn.toHostFn` is the one
bridge to the runtime's `HostFn`, and `HostEnv.allocate` places a resolved,
positional environment in the store in import order.
-/

namespace Wasm

/-- What a NEAR host function sees: the contract's memory and the host state. -/
structure HostStore (α : Type) where
  mem : Memory
  host : α

inductive HostResult (α : Type) where
  /-- The call returned; the store carries every effect. -/
  | Return (values : List Value) (st : HostStore α)
  /-- The call trapped; the store carries the effects before the trap. -/
  | Trap (st : HostStore α) (message : String)

/-- A NEAR host function with its declared signature. -/
structure NearHostFn (α : Type) where
  params : List ValType := []
  results : List ValType := []
  invoke : HostStore α → List Value → HostResult α

/-- A positional host environment: one function per function import, in
the module's import order. -/
structure HostEnv (α : Type) where
  funcs : List (NearHostFn α) := []

/-- A function import with its signature. -/
structure ImportDecl where
  «module» : String
  name : String
  params : List ValType := []
  results : List ValType := []
deriving Repr, Inhabited, DecidableEq

/-- The module's function imports, in order. -/
def Module.importDecls (m : Module) : List ImportDecl :=
  m.importedFuncTypes.map fun (module, name, ft) =>
    { module, name, params := ft.params, results := ft.results }

/-- A NEAR host function as a runtime host function. A caller without a
memory gets an empty one; NEAR contracts always declare a memory. -/
def NearHostFn.toHostFn (fn : NearHostFn α) : HostFn α :=
  { type := { params := fn.params, results := fn.results },
    call := fun host mem args =>
      match fn.invoke { mem := mem.getD (Memory.new 0 none), host } args with
      | .Return values st => .return values st.host (some st.mem)
      | .Trap st message => .trap (.host message) st.host (some st.mem) }

/-- Allocate the environment's functions in the store, returning the extern
values to instantiate the module with, in import order. -/
def HostEnv.allocate (store : Store α) (env : HostEnv α) : Store α × List ExternVal :=
  env.funcs.foldl (init := (store, [])) fun (store, exts) fn =>
    let (store, addr) := store.allocFunc (.host fn.toHostFn)
    (store, exts ++ [.func addr])

/-- The host functions of an allocated environment are the environment's. -/
theorem HostEnv.allocate_funcs (store : Store α) (env : HostEnv α) (fn : HostFn α)
    (h : FuncInst.host fn ∈ (env.allocate store).1.funcs) :
    FuncInst.host fn ∈ store.funcs ∨ ∃ nfn ∈ env.funcs, nfn.toHostFn = fn := by
  unfold HostEnv.allocate at h
  suffices key : ∀ (init : Store α × List ExternVal) (fns : List (NearHostFn α)),
      FuncInst.host fn ∈ (fns.foldl (fun (store, exts) fn =>
        let (store, addr) := store.allocFunc (.host fn.toHostFn)
        (store, exts ++ [.func addr])) init).1.funcs →
      FuncInst.host fn ∈ init.1.funcs ∨ ∃ nfn ∈ fns, nfn.toHostFn = fn by
    exact key (store, []) env.funcs h
  intro init fns
  induction fns generalizing init with
  | nil => intro h; exact Or.inl h
  | cons head tail ih =>
    intro h
    obtain ⟨st, exts⟩ := init
    simp only [List.foldl_cons] at h
    rcases ih _ h with hin | ⟨nfn, hmem, heq⟩
    · simp only [Store.allocFunc, Array.mem_push] at hin
      rcases hin with hin | hin
      · exact Or.inl hin
      · exact Or.inr ⟨head, List.mem_cons_self .., (FuncInst.host.inj hin).symm⟩
    · exact Or.inr ⟨nfn, List.mem_cons_of_mem _ hmem, heq⟩

/-- The host state of a store whose host functions came from an environment
is the one it was built with. -/
theorem HostEnv.allocate_host (store : Store α) (env : HostEnv α) :
    (env.allocate store).1.host = store.host := by
  unfold HostEnv.allocate
  suffices key : ∀ (init : Store α × List ExternVal) (fns : List (NearHostFn α)),
      (fns.foldl (fun (store, exts) fn =>
        let (store, addr) := store.allocFunc (.host fn.toHostFn)
        (store, exts ++ [.func addr])) init).1.host = init.1.host by
    exact key (store, []) env.funcs
  intro init fns
  induction fns generalizing init with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨st, exts⟩ := init
    simp only [List.foldl_cons]
    rw [ih]
    rfl

end Wasm
