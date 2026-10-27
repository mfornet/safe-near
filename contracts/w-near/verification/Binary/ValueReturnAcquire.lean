import Binary.ValueReturnBorrow

/-! Actual deployed RefCell acquisition descriptors f494 and f429. -/
namespace WNear.Binary.ValueReturnAcquire
open Wasm Wasm.Near
set_option maxRecDepth 20000

def guard : Expr :=
  [.local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 1,
   .i32_binop .add, .local_tee 1, .i32_const 1, .i32_relop .ge_s, .br_if 0]
def rejected : Expr := [.i32_const 0, .return]
def incrementTail : Expr := [.local_get 0, .local_get 1, .call 672, .drop, .local_get 0]
def incrementBody : Expr := [.block .empty (guard ++ rejected)] ++ incrementTail
def incrementFunction : Func := {type := 32, locals := [.num .i32], body := incrementBody, bodySize := 38}
def incrementSignature : FuncType := {params := [.num .i32], results := [.num .i32]}

def acquirePanic : Expr :=
  [.i32_const 1054673, .i32_const 24, .local_get 3, .i32_const 8, .i32_binop .add,
   .i32_const 1054868, .local_get 2, .call 881, .unreachable]
def acquirePrologue : Expr := [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 3, .global_set 0]
def acquireGuard : Expr := [.local_get 1, .call 494, .local_tee 4, .br_if 0]
def acquireTail : Expr :=
  [.local_get 0, .local_get 4, .store .i32 none {align := 2, offset := 4},
   .local_get 0, .local_get 1, .i32_const 4, .i32_binop .add, .store .i32 none {align := 2, offset := 0},
   .local_get 3, .i32_const 16, .i32_binop .add, .global_set 0]
def acquireBody : Expr := acquirePrologue ++ [.block .empty (acquireGuard ++ acquirePanic)] ++ acquireTail
def acquireFunction : Func := {type := 31, locals := [.num .i32, .num .i32], body := acquireBody, bodySize := 92}
def acquireSignature : FuncType := {params := [.num .i32, .num .i32, .num .i32], results := []}

theorem increment_function : wNearModule.funcs[446]? = some incrementFunction := by kernel_rfl
theorem increment_signature : wNearModule.types[32]? = some incrementSignature := by kernel_rfl
theorem acquire_function : wNearModule.funcs[381]? = some acquireFunction := by kernel_rfl
theorem acquire_signature : wNearModule.types[31]? = some acquireSignature := by kernel_rfl
theorem increment_activation (op : Nat) (cell : UInt32) :
    activationGas op #[.i32 cell, .i32 0] = 9 * op := by simp [activationGas]
theorem acquire_activation (op : Nat) (out cell location : UInt32) :
    activationGas op #[.i32 out, .i32 cell, .i32 location, .i32 0, .i32 0] = 11 * op := by simp [activationGas]

end WNear.Binary.ValueReturnAcquire
