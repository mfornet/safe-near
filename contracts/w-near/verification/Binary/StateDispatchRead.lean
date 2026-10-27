import Binary.StateDispatch

/-! Actual f435 initialized register-length dispatch instruction decomposition. -/
namespace WNear.Binary.StateDispatchRead
open Wasm

def prologue : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 3,.global_set 0]
def lookupAcquire : Expr := [.local_get 0,.load .i32 none {align := 2,offset := 0},.call_indirect 1 0,
  .local_tee 0,.i32_eqz,.br_if 0,.local_get 3,.local_get 0,.i32_const 1055160,.call 429]
def copyRecord : Expr := [.local_get 3,.local_get 3,.load .i32 none {align := 2,offset := 4},.store .i32 none {align := 2,offset := 12},
  .local_get 3,.local_get 3,.load .i32 none {align := 2,offset := 0},.local_tee 4,.store .i32 none {align := 2,offset := 8}]
def selectRecord : Expr := [.local_get 4,.i32_const 0,.local_get 4,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055208,.call 430]
def dispatch : Expr := [.local_tee 4,.load .i32 none {align := 2,offset := 0},.local_get 1,
  .load .i64 none {align := 3,offset := 0},.local_get 2,
  .load .i64 (some {bits := 32,signed := false}) {align := 2,offset := 0},
  .local_get 4,.load .i32 none {align := 2,offset := 4},.load .i32 none {align := 2,offset := 12},.call_indirect 4 0]
def cleanup : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.i32_const 4,.i32_binop .or,.call 431,.br 1]
def tail : Expr := copyRecord ++ [.i32_const 0,.local_set 0] ++ selectRecord ++ dispatch ++ cleanup

def fallback : Expr := [.call 762,.i32_const 1,.local_set 0]
def epilogue : Expr := [.local_get 0,.call 433,.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]
def body : Expr := prologue ++ [.block .empty ([.block .empty (lookupAcquire ++ tail)] ++ fallback)] ++ epilogue

def function : Func := {type := 31,locals := [.num .i32,.num .i32],body,bodySize := 183}
def signature : FuncType := {params := [.num .i32,.num .i32,.num .i32],results := []}

theorem module_function : wNearModule.funcs[387]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[31]? = some signature := by kernel_rfl
theorem body_eq : f435.body = body := by kernel_rfl
end WNear.Binary.StateDispatchRead
