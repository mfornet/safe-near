import WasmLogic.Examples.Stack.Code
import WasmLogic.Examples.Client.Bytes

/-!
# The client of the stack module

Iris-Wasm's `stack_client.v` (MIT licence): a module that imports the stack's
functions and table, puts `square` in table entry 0 with an element segment,
and runs `main` as its start function. `main` makes a stack, pushes 4 and 6,
maps `square` over it, pops 36 and 16 and stores their difference, 20, in the
exported global `answer`, or stores -1 if no stack could be made.
`client_decodes` proves that the decoder reads exactly `clientModule` from
`client.wasm`.
-/

namespace WasmLogic.Examples.Client

open Wasm WasmLogic.Examples.Stack

/-- Iris-Wasm's `main`. Function indices: 0 `new_stack`, 1 `is_empty`,
2 `is_full`, 3 `pop`, 4 `push`, 5 `stack_map`, 6 `stack_length` (imported),
7 `main`, 8 `square`. -/
def main : List Instr :=
  [.call 0, .local_tee 0, .i32_const 0xFFFFFFFF, .i32_relop .eq,
    .«if» .empty [.i32_const 0xFFFFFFFF, .global_set 0, .return] [],
    .local_get 0, .i32_const 4, .call 4,
    .local_get 0, .i32_const 6, .call 4,
    .local_get 0, .i32_const 0, .call 5,
    .local_get 0, .call 3,
    .local_get 0, .call 3,
    .i32_binop .sub, .global_set 0]

/-- Iris-Wasm's `square`. -/
def square : List Instr := [.local_get 0, .local_get 0, .i32_binop .mul]

def clientTypes : Array FuncType :=
  #[{ params := [], results := [] }, { params := [], results := [i32t] },
    { params := [i32t], results := [i32t] }, { params := [i32t, i32t], results := [] }]

def mainFunc : Func := { type := 0, locals := [i32t], body := main }

def squareFunc : Func := { type := 2, locals := [], body := square }

/-- The global `answer`: a mutable `i32`, initially 0. -/
def answerType : GlobalType := { type := i32t, mutable := true }

def clientModule : Module :=
  { types := clientTypes,
    imports := #[
      { module := "stack", name := "new_stack", desc := .func 1 },
      { module := "stack", name := "is_empty", desc := .func 2 },
      { module := "stack", name := "is_full", desc := .func 2 },
      { module := "stack", name := "pop", desc := .func 2 },
      { module := "stack", name := "push", desc := .func 3 },
      { module := "stack", name := "stack_map", desc := .func 3 },
      { module := "stack", name := "stack_length", desc := .func 2 },
      { module := "stack", name := "table",
        desc := .table { elem := .funcref, limits := { min := 1, max := none } } }],
    funcs := #[mainFunc, squareFunc],
    globals := #[{ type := answerType, init := [.i32_const 0] }],
    elems := #[{ type := .funcref, init := [[.ref_func 8]], mode := .active 0 [.i32_const 0] }],
    start := some 7,
    exports := #[{ name := "answer", desc := .global 0 }] }

theorem client_decodes : Binary.decode clientBytes = .ok clientModule := by
  kernel_rfl

end WasmLogic.Examples.Client
