import Binary.DeallocateAlign

/-! Actual page-rounding and checked page-byte helpers called by f577. -/
namespace WNear.Binary.AllocateGrowth
open Wasm Wasm.Near

def body569 : Expr := [.local_get 0,.i32_const 65536,.call 568]
def function569 : Func := {type:=32,locals:=[],body:=body569,bodySize:=14}
def signature569 : FuncType := {params:=[.num .i32],results:=[.num .i32]}
def panic573 : Expr := [.i32_const 1057216,.i32_const 33,.i32_const 1057188,.call 853,.unreachable]
def check573 : Expr := [.local_get 0,.i32_const 65535,.i32_binop .and,.local_get 0,.i32_relop .eq,.br_if 0]
def body573 : Expr := [.block .empty (check573++panic573),.local_get 0,.i32_const 16,.i32_binop .shl]
def function573 : Func := {type:=32,locals:=[],body:=body573,bodySize:=43}
def signature573 : FuncType := signature569

theorem module_function569 : wNearModule.funcs[521]?=some function569 := by kernel_rfl
theorem module_function573 : wNearModule.funcs[525]?=some function573 := by kernel_rfl
theorem module_signature : wNearModule.types[32]?=some signature569 := by kernel_rfl
end WNear.Binary.AllocateGrowth
