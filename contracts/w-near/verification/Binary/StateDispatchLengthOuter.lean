import Binary.StateDispatchLength

/-! Actual f524 register-length option-record wrapper. -/
namespace WNear.Binary.StateDispatchLengthOuter
open Wasm

def head : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 2,.global_set 0,
  .local_get 2,.local_get 1,.store .i64 none {align := 3,offset := 8},
  .local_get 0,.i32_const 1055020,.local_get 2,.i32_const 8,.i32_binop .add]
def tail : Expr := [.local_tee 1,.store .i64 none {align := 3,offset := 8},.local_get 0,.local_get 1,
  .i64_const 18446744073709551615,.i64_relop .ne,.cvt .i64_extend_i32_u,.store .i64 none {align := 3,offset := 0},
  .local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]
def body : Expr := head ++ [.call 440] ++ tail
def function : Func := {type := 5,locals := [.num .i32],body,bodySize := 74}
def signature : FuncType := {params := [.num .i32,.num .i64],results := []}

theorem module_function : wNearModule.funcs[476]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[5]? = some signature := by kernel_rfl
theorem body_eq : f524.body = body := by kernel_rfl
end WNear.Binary.StateDispatchLengthOuter
