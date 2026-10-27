import Binary.Module
import NearVM.Run

/-! Actual pointer/borrow checks and counter operations on f456's path. -/
namespace WNear.Binary.ValueReturnBorrow
open Wasm Wasm.Near
set_option maxRecDepth 20000

def nonnullPanic : Expr := [.i32_const 1055176, .i32_const 29, .local_get 1, .call 879, .unreachable]
def nonnullBody : Expr := [.block .empty ([.local_get 0, .br_if 0] ++ nonnullPanic), .local_get 0]
def nonnullFunction : Func := {type := 13, locals := [], body := nonnullBody, bodySize := 28}
def nonnullSignature : FuncType := {params := [.num .i32, .num .i32], results := [.num .i32]}

def checkPanic : Expr :=
  [.i32_const 1054165, .i32_const 70, .local_get 1, .i32_const 8, .i32_binop .add,
   .i32_const 1054900, .i32_const 1054316, .call 881, .unreachable]
def checkPrologue : Expr := [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 1, .global_set 0]
def checkEpilogue : Expr := [.local_get 1, .i32_const 16, .i32_binop .add, .global_set 0]
def checkBody : Expr := checkPrologue ++
  [.block .empty ([.local_get 0, .i32_eqz, .br_if 0] ++ checkPanic)] ++ checkEpilogue
def checkFunction : Func := {type := 0, locals := [.num .i32], body := checkBody, bodySize := 73}
def voidSignature : FuncType := {params := [.num .i32], results := []}

def swapBody : Expr :=
  [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_set 2,
   .local_get 0, .local_get 1, .store .i32 none {align := 2, offset := 0}, .local_get 2]
def swapFunction : Func := {type := 13, locals := [.num .i32], body := swapBody, bodySize := 20}

def releaseBody : Expr :=
  [.local_get 0, .load .i32 none {align := 2, offset := 0}, .local_tee 0,
   .local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_const 4294967295,
   .i32_binop .add, .call 672, .drop]
def releaseFunction : Func := {type := 0, locals := [], body := releaseBody, bodySize := 24}

theorem nonnull_function : wNearModule.funcs[382]? = some nonnullFunction := by kernel_rfl
theorem nonnull_signature : wNearModule.types[13]? = some nonnullSignature := by kernel_rfl
theorem check_function : wNearModule.funcs[385]? = some checkFunction := by kernel_rfl
theorem void_signature : wNearModule.types[0]? = some voidSignature := by kernel_rfl
theorem swap_function : wNearModule.funcs[624]? = some swapFunction := by kernel_rfl
theorem release_function : wNearModule.funcs[383]? = some releaseFunction := by kernel_rfl

theorem nonnull_activation (op : Nat) (ptr location : UInt32) :
    activationGas op #[.i32 ptr, .i32 location] = 9 * op := by simp [activationGas]
theorem check_activation (op : Nat) (status : UInt32) :
    activationGas op #[.i32 status, .i32 0] = 9 * op := by simp [activationGas]
theorem swap_activation (op : Nat) (ptr value : UInt32) :
    activationGas op #[.i32 ptr, .i32 value, .i32 0] = 10 * op := by simp [activationGas]
theorem release_activation (op : Nat) (ptr : UInt32) :
    activationGas op #[.i32 ptr] = 9 * op := by simp [activationGas]

end WNear.Binary.ValueReturnBorrow
