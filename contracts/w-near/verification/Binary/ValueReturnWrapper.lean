import Binary.Module
import NearVM.Run

namespace WNear.Binary.ValueReturnWrapper
open Wasm Wasm.Near
set_option maxRecDepth 20000

def prologue : Expr := [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 2, .global_set 0]
def saveSlice : Expr := [.local_get 2, .local_get 1, .store .i32 none {align := 2, offset := 12},
  .local_get 2, .local_get 0, .store .i32 none {align := 2, offset := 8}]
def arguments : Expr := [.i32_const 1055020, .local_get 2, .i32_const 8, .i32_binop .add]
def epilogue : Expr := [.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0]
def body : Expr := prologue ++ saveSlice ++ arguments ++ [.call 456] ++ epilogue
def function : Func := {type := 14, locals := [.num .i32], body, bodySize := 63}
def signature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem module_function : wNearModule.funcs[497]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl
end WNear.Binary.ValueReturnWrapper
