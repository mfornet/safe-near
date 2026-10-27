import Binary.StateDispatch

/-! Actual f440 initialized register-length dispatch instruction decomposition. -/
namespace WNear.Binary.StateDispatchLength
open Wasm

def prologue : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 2,.global_set 0]
def lookupAcquire : Expr := [.local_get 0,.load .i32 none {align := 2,offset := 0},.call_indirect 1 0,
  .local_tee 0,.i32_eqz,.br_if 0,.local_get 2,.local_get 0,.i32_const 1055224,.call 429]
def copyRecord : Expr := [.local_get 2,.local_get 2,.load .i32 none {align := 2,offset := 4},.store .i32 none {align := 2,offset := 12},
  .local_get 2,.local_get 2,.load .i32 none {align := 2,offset := 0},.local_tee 0,.store .i32 none {align := 2,offset := 8}]
def selectRecord : Expr := [.local_get 0,.i32_const 0,.local_get 0,.load .i32 none {align := 2,offset := 0},.select none,.i32_const 1055240,.call 430]
def dispatch : Expr := [.local_tee 0,.load .i32 none {align := 2,offset := 0},.local_get 1,.load .i64 none {align := 3,offset := 0},
  .local_get 0,.load .i32 none {align := 2,offset := 4},.load .i32 none {align := 2,offset := 16},.call_indirect 7 0]
def cleanup : Expr := [.local_set 3,.local_get 2,.i32_const 8,.i32_binop .add,.i32_const 4,.i32_binop .or,.call 431,.i64_const 0,.local_set 4,.br 1]
def tail : Expr := copyRecord ++ selectRecord ++ dispatch ++ cleanup

def fallback : Expr := [.call 762,.i64_const 1,.local_set 4]
def epilogue : Expr := [.local_get 4,.local_get 3,.call 432,.local_set 3,.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0,.local_get 3]
def body : Expr := prologue ++ [.block .empty ([.block .empty (lookupAcquire ++ tail)] ++ fallback)] ++ epilogue

def function : Func := {type := 30,locals := [.num .i32,.num .i64,.num .i64],body,bodySize := 188}
def signature : FuncType := {params := [.num .i32,.num .i32],results := [.num .i64]}

theorem module_function : wNearModule.funcs[392]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[30]? = some signature := by kernel_rfl
theorem body_eq : f440.body = body := by kernel_rfl
end WNear.Binary.StateDispatchLength
