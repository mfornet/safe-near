import Wasm.Store

/-!
# The `spectest` host module

What the specification's reference interpreter exports under the name
`spectest`, which the testsuite imports: printing functions that do nothing
here, four globals, a table and a memory.
-/

namespace Wasm.Host

def printFn (params : List ValType) : HostFn H :=
  { type := { params, results := [] }, call := fun h mem _ => .return [] h mem }

def spectest : HostModule H :=
  { funcs := [
      ("print", printFn []),
      ("print_i32", printFn [.i32]),
      ("print_i64", printFn [.i64]),
      ("print_f32", printFn [.f32]),
      ("print_f64", printFn [.f64]),
      ("print_i32_f32", printFn [.i32, .f32]),
      ("print_f64_f64", printFn [.f64, .f64])],
    globals := [
      ("global_i32", { type := .i32, mutable := false }, .i32 666),
      ("global_i64", { type := .i64, mutable := false }, .i64 666),
      ("global_f32", { type := .f32, mutable := false }, .f32 (666.6 : Float32).toBits),
      ("global_f64", { type := .f64, mutable := false }, .f64 (666.6 : Float).toBits)],
    tables := [("table", { elem := .funcref, limits := { min := 10, max := some 20 } })],
    mems := [("memory", { limits := { min := 1, max := some 2 } })] }

end Wasm.Host
