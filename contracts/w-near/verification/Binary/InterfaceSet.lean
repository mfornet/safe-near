import Binary.ValueReturnOuter

/-! Exact deployed normal setter f463 and its f520 caller. -/
namespace WNear.Binary.InterfaceSet
open Wasm Wasm.Near
set_option maxRecDepth 20000

def prologue : Expr := [.global_get 0, .i32_const 32, .i32_binop .sub, .local_tee 3, .global_set 0]
def saveArguments : Expr := [.local_get 3, .local_get 2, .store .i32 none {align := 2, offset := 20},
  .local_get 3, .local_get 1, .store .i32 none {align := 2, offset := 16}]
def lookup : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .call_indirect 1 0]
def acquire : Expr := [.local_tee 0, .i32_eqz, .br_if 0, .local_get 3, .i32_const 8,
  .i32_binop .add, .local_get 0, .i32_const 1055120, .call 441]
def copyBorrow : Expr := [.local_get 3, .local_get 3, .load .i32 none {align := 2, offset := 12},
  .store .i32 none {align := 2, offset := 28}, .local_get 3, .local_get 3,
  .load .i32 none {align := 2, offset := 8}, .local_tee 0, .store .i32 none {align := 2, offset := 24}]
def guard : Expr := [.local_get 0, .call 464]
def install : Expr := [.local_get 0, .local_get 2, .store .i32 none {align := 2, offset := 4},
  .local_get 0, .local_get 1, .store .i32 none {align := 2, offset := 0}]
def release : Expr := [.local_get 3, .i32_const 24, .i32_binop .add, .i32_const 4, .i32_binop .or,
  .call 442, .i32_const 0, .local_set 1, .br 1]
def inner : Expr := lookup ++ acquire ++ copyBorrow ++ guard ++ install ++ release
def fallback : Expr := [.call 762, .local_get 3, .i32_const 16, .i32_binop .add, .call 465, .i32_const 1, .local_set 1]
def epilogue : Expr := [.local_get 1, .call 433, .local_get 3, .i32_const 32, .i32_binop .add, .global_set 0]
def body : Expr := prologue ++ saveArguments ++ [.block .empty ([.block .empty inner] ++ fallback)] ++ epilogue
def function : Func := {type := 31, locals := [.num .i32], body, bodySize := 181}
def signature : FuncType := {params := [.num .i32, .num .i32, .num .i32], results := []}

def wrapperBody : Expr := [.i32_const 1055020, .local_get 0, .local_get 1, .call 463]
def wrapperFunction : Func := {type := 14, locals := [], body := wrapperBody, bodySize := 18}
def wrapperSignature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem body_eq : f463.body = body := rfl
theorem module_function : wNearModule.funcs[415]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[31]? = some signature := by kernel_rfl
theorem inner_length : inner.length = 38 := rfl
theorem wrapper_module_function : wNearModule.funcs[472]? = some wrapperFunction := by kernel_rfl
theorem wrapper_module_signature : wNearModule.types[14]? = some wrapperSignature := by kernel_rfl

theorem activation_cost (op : Nat) (interface receiver vtable : UInt32) :
  activationGas op #[.i32 interface, .i32 receiver, .i32 vtable, .i32 0] = 10 * op := by simp [activationGas]
theorem wrapper_activation_cost (op : Nat) (receiver vtable : UInt32) :
  activationGas op #[.i32 receiver, .i32 vtable] = 9 * op := by simp [activationGas]

end WNear.Binary.InterfaceSet
