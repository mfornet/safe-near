import Binary.StateDispatchLengthOuter

/-! Actual f523 register-vector reader, including its post-f435 copy order. -/
namespace WNear.Binary.StateDispatchRegisterOuter
open Wasm

def copyCode : Expr := [.local_get 0,.i32_const 8,.i32_binop .add,
  .local_get 2,.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,
  .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0},
  .local_get 0,.local_get 2,.load .i64 none {align:=3,offset:=32},.store .i64 none {align:=2,offset:=0}]
def epilogue : Expr := [.local_get 2,.i32_const 48,.i32_binop .add,.global_set 0]
def afterRead : Expr := copyCode++[.br 1]
def head : Expr := [.global_get 0,.i32_const 48,.i32_binop .sub,.local_tee 2,.global_set 0,
  .local_get 2,.local_get 1,.store .i64 none {align:=3,offset:=24},
  .local_get 2,.i32_const 8,.i32_binop .add,.local_get 1,.call 524]
def presentRead : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=8},.cvt .i32_wrap_i64,.i32_eqz,.br_if 0,
  .local_get 2,.i32_const 32,.i32_binop .add,.i32_const 0,.local_get 2,
  .load .i64 none {align:=3,offset:=16},.cvt .i32_wrap_i64,.call 687,
  .i32_const 1055020,.local_get 2,.i32_const 24,.i32_binop .add,
  .local_get 2,.i32_const 32,.i32_binop .add,.call 435]
def fallback : Expr := [.call 761,.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0}]
def body : Expr := head++[.block .empty ([.block .empty (presentRead++afterRead)]++fallback)]++epilogue

def function : Func := {type:=5,locals:=[.num .i32],body,bodySize:=152}
def signature : FuncType := {params:=[.num .i32,.num .i64],results:=[]}
theorem module_function : wNearModule.funcs[475]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[5]? = some signature := by kernel_rfl
theorem body_eq : f523.body = body := by kernel_rfl
end WNear.Binary.StateDispatchRegisterOuter
