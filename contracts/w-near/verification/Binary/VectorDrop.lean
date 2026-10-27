import Binary.Module
import NearVM.Run

/-! Actual vector destruction wrappers. The nonempty path eventually reaches
f237 and the allocator; this file records code without asserting heap safety. -/
namespace WNear.Binary.VectorDrop
open Wasm Wasm.Near
set_option maxRecDepth 20000

def signature : FuncType := {params := [.num .i32], results := []}
def tripleSignature : FuncType := {params := [.num .i32, .num .i32, .num .i32], results := []}
def body68 : Expr := [.local_get 0, .call 778, .local_get 0, .call 747]
def function68 : Func := {type := 0, locals := [], body := body68, bodySize := 18}
def function778 : Func := {type := 0, locals := [], body := [], bodySize := 2}
def vectorGuard : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 4}, .local_tee 1, .i32_eqz, .br_if 0]
def vectorTail : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_get 1, .i32_const 1, .call 777]
def body747 : Expr := [.block .empty (vectorGuard ++ vectorTail)]
def function747 : Func := {type := 0, locals := [.num .i32], body := body747, bodySize := 32}
def capacityGuard : Expr := [.local_get 1, .i32_eqz, .br_if 0]
def capacityTail : Expr := [.local_get 0, .local_get 1, .local_get 2, .call 311]
def body777 : Expr := [.block .empty (capacityGuard ++ capacityTail)]
def function777 : Func := {type := 31, locals := [], body := body777, bodySize := 22}
def body311 : Expr := [.local_get 0, .local_get 1, .local_get 2, .call 237, .return]
def function311 : Func := {type := 31, locals := [], body := body311, bodySize := 15}

theorem module68 : wNearModule.funcs[20]? = some function68 := by kernel_rfl
theorem module778 : wNearModule.funcs[730]? = some function778 := by kernel_rfl
theorem module747 : wNearModule.funcs[699]? = some function747 := by kernel_rfl
theorem module777 : wNearModule.funcs[729]? = some function777 := by kernel_rfl
theorem module311 : wNearModule.funcs[263]? = some function311 := by kernel_rfl
theorem module_signature : wNearModule.types[0]? = some signature := by kernel_rfl
theorem module_tripleSignature : wNearModule.types[31]? = some tripleSignature := by kernel_rfl
end WNear.Binary.VectorDrop
