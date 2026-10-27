import Binary.ValueReturnDispatch
import Binary.ValueReturnBorrow

/-! Exact deployed outer value-return body and its normal-path fragments. -/
namespace WNear.Binary.ValueReturnOuter
open Wasm Wasm.Near
set_option maxRecDepth 20000

def prologue : Expr := ValueReturnBorrow.checkPrologue.map fun i =>
  match i with | .local_tee 1 => .local_tee 2 | _ => i

def lookup : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .call_indirect 1 0]
def acquire : Expr := [.local_tee 0, .i32_eqz, .br_if 0,
  .local_get 2, .local_get 0, .i32_const 1056148, .call 429]
def saveBorrow : Expr :=
  [.local_get 2, .local_get 2, .load .i32 none {align := 2, offset := 4},
   .store .i32 none {align := 2, offset := 12}, .local_get 2, .local_get 2,
   .load .i32 none {align := 2, offset := 0}, .local_tee 3,
   .store .i32 none {align := 2, offset := 8}, .i32_const 0, .local_set 0]
def nonnull : Expr := [.local_get 3, .i32_const 0, .local_get 3,
  .load .i32 none {align := 2, offset := 0}, .select none, .i32_const 1056164, .call 430]
def cleanup : Expr := [.local_get 2, .i32_const 8, .i32_binop .add,
  .i32_const 4, .i32_binop .or, .call 431, .br 1]
def inner : Expr := lookup ++ acquire ++ saveBorrow ++ nonnull ++ ValueReturnDispatch.dispatch ++ cleanup
def fallback : Expr := [.call 762, .i32_const 1, .local_set 0]
def epilogue : Expr := [.local_get 0, .call 433, .local_get 2, .i32_const 16, .i32_binop .add, .global_set 0]
def body : Expr := prologue ++ [.block .empty ([.block .empty inner] ++ fallback)] ++ epilogue
def function : Func := {type := 14, locals := [.num .i32, .num .i32], body, bodySize := 183}
def signature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem body_eq : f456.body = body := by rfl
theorem inner_eq : ValueReturnDispatch.innerBody = inner := by rfl
theorem module_function : wNearModule.funcs[408]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl
theorem inner_length : inner.length = 45 := rfl
theorem activation_cost (op : Nat) (interface slice : UInt32) :
  activationGas op #[.i32 interface, .i32 slice, .i32 0, .i32 0] = 10 * op := by
  simp [activationGas]

end WNear.Binary.ValueReturnOuter
