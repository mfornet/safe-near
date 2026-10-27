import Binary.Module
import NearVM.Run

/-! Actual deployed panic-hook replacement f822. -/
namespace WNear.Binary.PanicHookSet
open Wasm Wasm.Near
set_option maxRecDepth 20000

def initializationGuard : Expr := [.i32_const 0, .load .i32 none {align := 2, offset := 1074932}, .i32_eqz, .br_if 0]
def initializationSlow : Expr := [.call 792, .i32_eqz, .br_if 1]
def lock : Expr := [.i32_const 0, .load .i32 none {align := 2, offset := 1074920}, .local_set 2,
  .i32_const 0, .i32_const 4294967295, .store .i32 none {align := 2, offset := 1074920}, .local_get 2, .br_if 1]
def replaceVtable : Expr := [.i32_const 0, .load .i32 none {align := 2, offset := 1074928}, .local_set 2,
  .i32_const 0, .local_get 1, .store .i32 none {align := 2, offset := 1074928}]
def replaceReceiver : Expr := [.i32_const 0, .load .i32 none {align := 2, offset := 1074924}, .local_set 1,
  .i32_const 0, .local_get 0, .store .i32 none {align := 2, offset := 1074924}]
def unlock : Expr := [.i32_const 0, .i32_const 0, .store .i32 none {align := 2, offset := 1074920}]
def dropGuard : Expr := [.local_get 2, .i32_eqz, .br_if 0]
def dropSlow : Expr := [.local_get 1, .local_get 2, .load .i32 none {align := 2, offset := 0}, .call_indirect 0 0,
  .local_get 2, .load .i32 none {align := 2, offset := 4}, .local_tee 0, .i32_eqz, .br_if 0,
  .local_get 1, .local_get 0, .local_get 2, .load .i32 none {align := 2, offset := 8}, .call 311]
def accepted : Expr := [.block .empty (initializationGuard ++ initializationSlow)] ++ lock ++ replaceVtable ++
  replaceReceiver ++ unlock ++ [.block .empty (dropGuard ++ dropSlow), .return]
def rejected : Expr := [.i32_const 1066232, .i32_const 52, .i32_const 1066312, .call 803, .unreachable]
def body : Expr := [.block .empty ([.block .empty accepted] ++ rejected), .unreachable, .unreachable]
def function : Func := {type := 14, locals := [.num .i32], body, bodySize := 186}
def signature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem module_function : wNearModule.funcs[774]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl
theorem activation_cost (op : Nat) (receiver vtable : UInt32) :
    activationGas op #[.i32 receiver, .i32 vtable, .i32 0] = 10 * op := by simp [activationGas]

end WNear.Binary.PanicHookSet
