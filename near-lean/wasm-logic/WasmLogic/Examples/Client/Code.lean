import WasmLogic.Examples.Stack.Code
import WasmLogic.Examples.Client.Bytes

/-!
# A client of the stack module

`client.wat` imports `new_stack`, `push` and `pop` from the stack module and
exports `main`, which pushes 4 and 6 on a new stack and returns the
difference of the two values it pops back, or `-1` if no stack could be
made. `client_decodes` proves that the decoder reads exactly `clientModule`
from `client.wasm`.
-/

namespace WasmLogic.Examples.Client

open Wasm WasmLogic.Examples.Stack

def mainBody : List Instr :=
  [.call 0, .local_tee 0, .i32_const 0xFFFFFFFF, .i32_relop .eq,
    .«if» (.val (.num .i32)) [.i32_const 0xFFFFFFFF]
      [.local_get 0, .i32_const 4, .call 1,
        .local_get 0, .i32_const 6, .call 1,
        .local_get 0, .call 2, .local_get 0, .call 2, .i32_binop .sub]]

def clientTypes : Array FuncType :=
  #[{ params := [], results := [i32t] }, { params := [i32t, i32t], results := [] },
    { params := [i32t], results := [i32t] }]

def mainFunc : Func := { type := 0, locals := [i32t], body := mainBody }

def clientModule : Module :=
  { types := clientTypes,
    imports := #[
      { module := "stack", name := "new_stack", desc := .func 0 },
      { module := "stack", name := "push", desc := .func 1 },
      { module := "stack", name := "pop", desc := .func 2 }],
    funcs := #[mainFunc],
    exports := #[{ name := "main", desc := .func 3 }] }

theorem client_decodes : Binary.decode clientBytes = .ok clientModule := by
  kernel_rfl

end WasmLogic.Examples.Client
