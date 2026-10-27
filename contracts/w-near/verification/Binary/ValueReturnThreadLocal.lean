import Binary.Module
import NearVM.Run

namespace WNear.Binary.ValueReturnThreadLocal
open Wasm Wasm.Near
set_option maxRecDepth 20000

def lazyTail : Expr := [.local_get 0, .local_get 1, .call 467, .return]
def resultTail : Expr := [.local_get 0, .i32_const 4, .i32_binop .add]
def guard : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0},
  .i32_const 1, .i32_relop .eq, .br_if 0]
def body : Expr := [.block .empty (guard ++ lazyTail)] ++ resultTail
def function : Func := {type := 13, locals := [], body, bodySize := 31}
def signature : FuncType := {params := [.num .i32, .num .i32], results := [.num .i32]}
def lookupBody : Expr := [.i32_const 1074900, .i32_const 106, .call 468]
def lookupFunction : Func := {type := 1, locals := [], body := lookupBody, bodySize := 20}
def lookupSignature : FuncType := {params := [], results := [.num .i32]}

theorem module_function : wNearModule.funcs[420]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[13]? = some signature := by kernel_rfl
theorem lookup_function : wNearModule.funcs[517]? = some lookupFunction := by kernel_rfl
theorem lookup_signature : wNearModule.types[1]? = some lookupSignature := by kernel_rfl
end WNear.Binary.ValueReturnThreadLocal
