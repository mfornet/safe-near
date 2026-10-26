import WasmLogic.Tactic
import WasmLogic.Examples.Stack.Bytes

/-!
# The stack module of Iris-Wasm

The code of Iris-Wasm's stack case study (`theories/iris/examples/stack/`,
MIT licence), fragment by fragment under the same names, and the module they
form. `stack_decodes` proves that the decoder reads exactly this module from
the bytes of `stack.wasm`, compiled from `stack.wat` by the pinned
wasm-tools: the specifications in `Specs.lean` are about the binary.
-/

namespace WasmLogic.Examples.Stack

open Wasm

/-- `BI_load T_i32 None 0 0` / `BI_store T_i32 None 0 0`: alignment 2^0, offset 0. -/
abbrev a0 : MemArg := ⟨0, 0⟩

/-- `validate_stack x`: trap unless local `x` is a multiple of 65536. -/
def validate_stack (x : Nat) : List Instr :=
  [.local_get x, .i32_const 65536, .i32_binop .rem_u, .«if» .empty [.unreachable] []]

/-- `validate_stack_bound x`: trap unless the stack pointer cell is in bounds. -/
def validate_stack_bound (x : Nat) : List Instr :=
  [.local_get x, .load .i32 none a0, .drop]

def is_empty_op : List Instr :=
  [.local_get 0, .local_get 0, .load .i32 none a0, .i32_relop .eq]

def is_empty : List Instr := validate_stack 0 ++ validate_stack_bound 0 ++ is_empty_op

def is_full_op : List Instr :=
  [.i32_const 1, .i32_const 0, .local_get 0, .load .i32 none a0, .i32_const 65536,
    .i32_binop .rem_u, .i32_const 65532, .i32_relop .eq, .select none]

def is_full : List Instr := validate_stack 0 ++ validate_stack_bound 0 ++ is_full_op

def push_op : List Instr :=
  is_full_op ++
  [.«if» .empty [.unreachable] [],
    .local_get 0, .load .i32 none a0, .i32_const 4, .i32_binop .add, .local_tee 2,
    .local_get 1, .store .i32 none a0,
    .local_get 0, .local_get 2, .store .i32 none a0]

def push : List Instr := validate_stack 0 ++ validate_stack_bound 0 ++ push_op

def pop_op : List Instr :=
  is_empty_op ++
  [.«if» .empty [.unreachable] [],
    .local_get 0, .load .i32 none a0, .local_tee 1, .load .i32 none a0,
    .local_get 0, .local_get 1, .i32_const 4, .i32_binop .sub, .store .i32 none a0]

def pop : List Instr := validate_stack 0 ++ validate_stack_bound 0 ++ pop_op

def length_stack_op : List Instr :=
  [.local_get 0, .load .i32 none a0, .local_get 0, .i32_binop .sub, .i32_const 4,
    .i32_binop .div_u]

def length_stack : List Instr := validate_stack 0 ++ validate_stack_bound 0 ++ length_stack_op

def new_stack : List Instr :=
  [.i32_const 1, .memory_grow, .local_tee 0, .i32_const 0xFFFFFFFF, .i32_relop .eq,
    .«if» (.val (.num .i32)) [.i32_const 0xFFFFFFFF]
      [.local_get 0, .i32_const 65536, .i32_binop .mul, .local_tee 0, .local_get 0,
        .store .i32 none a0, .local_get 0]]

def map_initialise : List Instr :=
  [.local_get 0, .load .i32 none a0, .local_set 3, .local_get 0, .local_set 2]

def map_loop_body : List Instr :=
  [.local_get 2, .local_get 3, .i32_relop .eq, .br_if 1,
    .local_get 2, .i32_const 4, .i32_binop .add, .local_tee 2,
    .local_get 2, .load .i32 none a0, .local_get 1, .call_indirect 1 0, .store .i32 none a0,
    .br 0]

def map_op : List Instr := map_initialise ++ [.block .empty [.loop .empty map_loop_body]]

def stack_map : List Instr := validate_stack 0 ++ validate_stack_bound 0 ++ map_op

def i32t : ValType := .num .i32

def stackTypes : Array FuncType :=
  #[{ params := [], results := [i32t] }, { params := [i32t], results := [i32t] },
    { params := [i32t, i32t], results := [] }]

def stackModule : Module :=
  { types := stackTypes,
    funcs := #[
      { type := 0, locals := [i32t], body := new_stack, bodySize := 35 },
      { type := 1, locals := [], body := is_empty, bodySize := 27 },
      { type := 1, locals := [], body := is_full, bodySize := 39 },
      { type := 1, locals := [i32t], body := pop, bodySize := 53 },
      { type := 2, locals := [i32t], body := push, bodySize := 67 },
      { type := 2, locals := [i32t, i32t], body := stack_map, bodySize := 67 },
      { type := 1, locals := [], body := length_stack, bodySize := 30 }],
    tables := #[{ type := { elem := .funcref, limits := { min := 1, max := none } } }],
    mems := #[{ type := { limits := { min := 0, max := none } } }],
    exports := #[
      { name := "new_stack", desc := .func 0 }, { name := "is_empty", desc := .func 1 },
      { name := "is_full", desc := .func 2 }, { name := "pop", desc := .func 3 },
      { name := "push", desc := .func 4 }, { name := "stack_map", desc := .func 5 },
      { name := "stack_length", desc := .func 6 }, { name := "table", desc := .table 0 }] }

/-- The decoder reads exactly `stackModule` from the bytes of `stack.wasm`;
checked by the kernel. -/
theorem stack_decodes : Binary.decode stackBytes = .ok stackModule := by
  kernel_rfl

end WasmLogic.Examples.Stack
