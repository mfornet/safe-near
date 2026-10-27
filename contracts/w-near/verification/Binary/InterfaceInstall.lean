import Binary.Module
import NearVM.Run

/-! Exact deployed interface replacement guard and setter wrapper. -/
namespace WNear.Binary.InterfaceInstall
open Wasm Wasm.Near
set_option maxRecDepth 20000

def guardBody : Expr := [.block .empty
  [.local_get 0, .load .i32 none {align := 2, offset := 0}, .i32_eqz,
   .br_if 0, .local_get 0, .call 465]]
def guardFunction : Func := {type := 0, locals := [], body := guardBody, bodySize := 21}
def guardSignature : FuncType := {params := [.num .i32], results := []}
def wrapperBody : Expr := [.i32_const 1055020, .local_get 0, .local_get 1, .call 463]
def wrapperFunction : Func := {type := 14, locals := [], body := wrapperBody, bodySize := 18}
def wrapperSignature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem guard_function : wNearModule.funcs[416]? = some guardFunction := by kernel_rfl
theorem guard_signature : wNearModule.types[0]? = some guardSignature := by kernel_rfl
theorem wrapper_function : wNearModule.funcs[472]? = some wrapperFunction := by kernel_rfl
theorem wrapper_signature : wNearModule.types[14]? = some wrapperSignature := by kernel_rfl

theorem guard_activation (op : Nat) (pointer : UInt32) : activationGas op #[.i32 pointer] = 9 * op := by
  simp [activationGas]
theorem wrapper_activation (op : Nat) (receiver vtable : UInt32) :
    activationGas op #[.i32 receiver, .i32 vtable] = 9 * op := by simp [activationGas]

end WNear.Binary.InterfaceInstall
