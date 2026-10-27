import Binary.Module
import NearVM.Run

/-! Deployed checked ceiling division used by the heap deallocator. -/
namespace WNear.Binary.DeallocateAlign
open Wasm Wasm.Near
set_option maxRecDepth 20000

def overflowAdd : Expr := [.i32_const 1057104, .i32_const 28, .i32_const 1057088, .call 853, .unreachable]
def overflowSub : Expr := [.i32_const 1057152, .i32_const 33, .i32_const 1057132, .call 853, .unreachable]
def accepted : Expr :=
  [.local_get 0, .local_get 1, .i32_binop .add, .local_tee 2, .local_get 0, .i32_relop .lt_u, .br_if 0,
   .local_get 2, .i32_const 4294967295, .i32_binop .add, .local_tee 0, .local_get 2, .i32_relop .gt_u, .br_if 1,
   .local_get 0, .local_get 1, .i32_binop .div_u, .return]
def body568 : Expr := [.block .empty ([.block .empty accepted] ++ overflowAdd)] ++ overflowSub
def function568 : Func := {type := 13, locals := [.num .i32], body := body568, bodySize := 82}
def signature568 : FuncType := {params := [.num .i32, .num .i32], results := [.num .i32]}
def body570 : Expr := [.local_get 0, .i32_const 4, .call 568]
def function570 : Func := {type := 32, locals := [], body := body570, bodySize := 12}
def signature570 : FuncType := {params := [.num .i32], results := [.num .i32]}

theorem module_function568 : wNearModule.funcs[520]? = some function568 := by kernel_rfl
theorem module_signature568 : wNearModule.types[13]? = some signature568 := by kernel_rfl
theorem module_function570 : wNearModule.funcs[522]? = some function570 := by kernel_rfl
theorem module_signature570 : wNearModule.types[32]? = some signature570 := by kernel_rfl
end WNear.Binary.DeallocateAlign
