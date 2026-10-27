import Binary.ValueReturnAcquire

/-! Actual exclusive RefCell borrow helpers on the deployed interface setter. -/
namespace WNear.Binary.InterfaceBorrow
open Wasm Wasm.Near
set_option maxRecDepth 20000

def takeInit : Expr := [.i32_const 0, .local_set 1]
def takeGuard : Expr := [.local_get 0, .load .i32 none {align := 2, offset := 0}, .br_if 0]
def takeTail : Expr := [.local_get 0, .i32_const 4294967295, .call 672, .drop, .local_get 0, .local_set 1]
def takeBody : Expr := takeInit ++ [.block .empty (takeGuard ++ takeTail)] ++ [.local_get 1]
def takeFunction : Func := {type := 32, locals := [.num .i32], body := takeBody, bodySize := 35}
abbrev takeSignature : FuncType := ValueReturnAcquire.incrementSignature

def acquirePanic : Expr :=
  [.i32_const 1054657, .i32_const 16, .local_get 3, .i32_const 8, .i32_binop .add,
   .i32_const 1054852, .local_get 2, .call 881, .unreachable]
def acquireGuard : Expr := [.local_get 1, .call 492, .local_tee 4, .br_if 0]
def acquireBody : Expr := ValueReturnAcquire.acquirePrologue ++
  [.block .empty (acquireGuard ++ acquirePanic)] ++ ValueReturnAcquire.acquireTail
def acquireFunction : Func := {type := 31, locals := [.num .i32, .num .i32], body := acquireBody, bodySize := 92}
abbrev acquireSignature : FuncType := ValueReturnAcquire.acquireSignature

def releaseBody : Expr :=
  [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_tee 0, .local_get 0,
   .load .i32 none {align := 2, offset := 0}, .i32_const 1, .i32_binop .add, .call 672, .drop]
def releaseFunction : Func := {type := 0, locals := [], body := releaseBody, bodySize := 24}
abbrev releaseSignature : FuncType := ValueReturnBorrow.voidSignature

theorem take_function : wNearModule.funcs[444]? = some takeFunction := by kernel_rfl
theorem take_signature : wNearModule.types[32]? = some takeSignature := by kernel_rfl
theorem acquire_function : wNearModule.funcs[393]? = some acquireFunction := by kernel_rfl
theorem acquire_signature : wNearModule.types[31]? = some acquireSignature := by kernel_rfl
theorem release_function : wNearModule.funcs[394]? = some releaseFunction := by kernel_rfl
theorem release_signature : wNearModule.types[0]? = some releaseSignature := by kernel_rfl

end WNear.Binary.InterfaceBorrow
