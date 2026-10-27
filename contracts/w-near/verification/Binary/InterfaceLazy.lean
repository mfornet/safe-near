import Binary.Module
import NearVM.Run

/-! Actual lazy initialization path f467, including its old-state drop guard. -/
namespace WNear.Binary.InterfaceLazy
open Wasm Wasm.Near
set_option maxRecDepth 20000

def reserve : Expr := [.global_get 0, .i32_const 48, .i32_binop .sub, .local_tee 2, .global_set 0]
def initCall : Expr := [.local_get 2, .local_get 1, .call_indirect 0 0]
def exchange64 : Expr := [.local_get 0, .load .i64 none {align := 2, offset := 4}, .local_set 3,
  .local_get 0, .local_get 2, .load .i64 none {align := 3, offset := 0}, .store .i64 none {align := 2, offset := 4}]
def exchange32 : Expr := [.local_get 0, .i32_const 12, .i32_binop .add, .local_tee 1,
  .load .i32 none {align := 2, offset := 0}, .local_set 4,
  .local_get 1, .local_get 2, .i32_const 8, .i32_binop .add,
  .load .i32 none {align := 2, offset := 0}, .store .i32 none {align := 2, offset := 0}]
def status : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_set 1,
  .local_get 0, .i32_const 1, .store .i32 none {align := 2, offset := 0}]
def saveOld : Expr := [.local_get 2, .i32_const 16, .i32_binop .add, .i32_const 12,
  .i32_binop .add, .local_get 4, .store .i32 none {align := 2, offset := 0},
  .local_get 2, .local_get 1, .store .i32 none {align := 2, offset := 16},
  .local_get 2, .local_get 3, .store .i64 none {align := 2, offset := 20}]
def result : Expr := [.local_get 0, .i32_const 4, .i32_binop .add, .local_set 0]
def dropOld : Expr := [.local_get 2, .i32_const 16, .i32_binop .add, .i32_const 8, .i32_binop .add, .call 464]
def guard : Expr := [.block .empty ([.local_get 1, .i32_eqz, .br_if 0] ++ dropOld)]
def restore : Expr := [.local_get 2, .i32_const 48, .i32_binop .add, .global_set 0, .local_get 0]
def body : Expr := reserve ++ initCall ++ exchange64 ++ exchange32 ++ status ++ saveOld ++ result ++ guard ++ restore
def function : Func := {type := 13, locals := [.num .i32, .num .i64, .num .i32], body, bodySize := 161}
def signature : FuncType := {params := [.num .i32, .num .i32], results := [.num .i32]}

theorem module_function : wNearModule.funcs[419]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[13]? = some signature := by kernel_rfl
theorem body_length : body.length = 56 := rfl
end WNear.Binary.InterfaceLazy
