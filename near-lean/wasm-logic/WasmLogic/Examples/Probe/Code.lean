import WasmLogic.Examples.Stack.Code
import WasmLogic.Examples.Probe.Bytes

/-!
# A probe of the stack's other functions

`probe.wat` imports `new_stack`, `is_empty`, `is_full`, `push` and
`stack_length`, and its start function records their results on a fresh
stack in the exported global `answer`: 1001, or -1 if no stack could be
made. It reaches, from instantiation, the specifications Iris-Wasm's client
does not use. `probe_decodes` proves that the decoder reads exactly
`probeModule` from `probe.wasm`.
-/

namespace WasmLogic.Examples.Probe

open Wasm WasmLogic.Examples.Stack

/-- Function indices: 0 `new_stack`, 1 `is_empty`, 2 `is_full`, 3 `push`,
4 `stack_length` (imported), 5 `main`. -/
def main : List Instr :=
  [.call 0, .local_tee 0, .i32_const 0xFFFFFFFF, .i32_relop .eq,
    .«if» .empty [.i32_const 0xFFFFFFFF, .global_set 0, .return] [],
    .local_get 0, .call 1,
    .local_get 0, .i32_const 4, .call 3,
    .local_get 0, .call 1, .i32_const 10, .i32_binop .mul, .i32_binop .add,
    .local_get 0, .call 2, .i32_const 100, .i32_binop .mul, .i32_binop .add,
    .local_get 0, .call 4, .i32_const 1000, .i32_binop .mul, .i32_binop .add,
    .global_set 0]

def probeTypes : Array FuncType :=
  #[{ params := [], results := [] }, { params := [], results := [i32t] },
    { params := [i32t], results := [i32t] }, { params := [i32t, i32t], results := [] }]

def mainFunc : Func := { type := 0, locals := [i32t], body := main }

def answerType : GlobalType := { type := i32t, mutable := true }

def probeModule : Module :=
  { types := probeTypes,
    imports := #[
      { module := "stack", name := "new_stack", desc := .func 1 },
      { module := "stack", name := "is_empty", desc := .func 2 },
      { module := "stack", name := "is_full", desc := .func 2 },
      { module := "stack", name := "push", desc := .func 3 },
      { module := "stack", name := "stack_length", desc := .func 2 }],
    funcs := #[mainFunc],
    globals := #[{ type := answerType, init := [.i32_const 0] }],
    start := some 5,
    exports := #[{ name := "answer", desc := .global 0 }] }

theorem probe_decodes : Binary.decode probeBytes = .ok probeModule := by
  kernel_rfl

end WasmLogic.Examples.Probe
