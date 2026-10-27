import Binary.Module
import NearVM.Run

/-! Actual f509 zero-size allocation-result path. -/
namespace WNear.Binary.PanicAllocateZero
open Wasm Wasm.Near
set_option maxRecDepth 20000

def allocator : Expr :=
  [.block .empty
    [.block .empty [.local_get 3, .i32_eqz, .br_if 0, .local_get 1, .local_get 2, .call 313, .local_set 2, .br 1],
      .local_get 1, .local_get 2, .call 310, .local_set 2],
   .local_get 2, .br_if 1, .call 707, .i32_const 0, .local_set 2, .br 1]
def zeroGuard : Expr := [.local_get 1, .i32_eqz, .br_if 0]
def reset : Expr := [.i32_const 0, .local_set 1]
def stores : Expr := [.local_get 0, .local_get 1, .store .i32 none {align := 2, offset := 4},
  .local_get 0, .local_get 2, .store .i32 none {align := 2, offset := 0}]
def body : Expr := [.block .empty [.block .empty (zeroGuard ++ allocator), .i32_const 0, .local_set 1]] ++ stores
def function : Func := {type := 45, locals := [], body, bodySize := 84}
def signature : FuncType := {params := [.num .i32, .num .i32, .num .i32, .num .i32], results := []}

theorem module_function : wNearModule.funcs[461]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[45]? = some signature := by kernel_rfl

theorem activation_cost (op : Nat) (out size alignment flag : UInt32) :
  activationGas op #[.i32 out, .i32 size, .i32 alignment, .i32 flag] = 10 * op := by simp [activationGas]
end WNear.Binary.PanicAllocateZero
