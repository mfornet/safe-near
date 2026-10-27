import Binary.InterfaceSet

/-! Exact deployed allocation wrappers used by the panic hook. -/
namespace WNear.Binary.PanicAllocate
open Wasm Wasm.Near
set_option maxRecDepth 20000

def prologue508 : Expr := [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 3, .global_set 0]
def arguments508 : Expr := [.local_get 3, .i32_const 8, .i32_binop .add, .local_get 1, .local_get 2, .i32_const 0]
def copies508 : Expr := [.local_get 0, .local_get 3, .load .i32 none {align := 2, offset := 8},
  .store .i32 none {align := 2, offset := 0}, .local_get 0, .local_get 3,
  .load .i32 none {align := 2, offset := 12}, .store .i32 none {align := 2, offset := 4}]
def epilogue508 : Expr := [.local_get 3, .i32_const 16, .i32_binop .add, .global_set 0]
def body508 : Expr := prologue508 ++ arguments508 ++ [.call 509] ++ copies508 ++ epilogue508
def function508 : Func := {type := 31, locals := [.num .i32], body := body508, bodySize := 69}
def signature508 : FuncType := {params := [.num .i32, .num .i32, .num .i32], results := []}

def prologue503 : Expr := [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 2, .global_set 0]
def arguments503 : Expr := [.local_get 2, .i32_const 8, .i32_binop .add, .local_get 0, .local_get 1]
def guard503 : Expr := [.local_get 2, .load .i32 none {align := 2, offset := 8}, .local_tee 3, .br_if 0,
  .local_get 0, .local_get 1, .call 842, .unreachable]
def epilogue503 : Expr := [.local_get 2, .i32_const 16, .i32_binop .add, .global_set 0, .local_get 3]
def body503 : Expr := prologue503 ++ arguments503 ++ [.call 508, .block .empty guard503] ++ epilogue503
def function503 : Func := {type := 13, locals := [.num .i32, .num .i32], body := body503, bodySize := 72}
def signature503 : FuncType := {params := [.num .i32, .num .i32], results := [.num .i32]}

theorem body508_eq : f508.body = body508 := rfl
theorem body503_eq : f503.body = body503 := rfl
theorem module_function508 : wNearModule.funcs[460]? = some function508 := by kernel_rfl
theorem module_function503 : wNearModule.funcs[455]? = some function503 := by kernel_rfl
theorem module_signature508 : wNearModule.types[31]? = some signature508 := by kernel_rfl
theorem module_signature503 : wNearModule.types[13]? = some signature503 := by kernel_rfl
theorem body508_length : body508.length = 24 := rfl
theorem body503_length : body503.length = 17 := rfl

theorem activation508 (op : Nat) (out size align : UInt32) :
    activationGas op #[.i32 out, .i32 size, .i32 align, .i32 0] = 10 * op := by simp [activationGas]
theorem activation503 (op : Nat) (size align : UInt32) :
    activationGas op #[.i32 size, .i32 align, .i32 0, .i32 0] = 10 * op := by simp [activationGas]

end WNear.Binary.PanicAllocate
