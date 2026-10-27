import Binary.Module
import NearVM.Run

/-! The deployed trait-method implementation f260 forwards to env.value_return.
Its unused receiver is an i32; the two host arguments are actual i64 values. -/
namespace WNear.Binary.ValueReturnLeaf
open Wasm Wasm.Near
set_option maxRecDepth 20000

def body : Expr := [.local_get 1, .local_get 2, .call 20]
def function : Func := {type := 4, locals := [], body, bodySize := 12}
def signature : FuncType := {params := [.num .i32, .num .i64, .num .i64], results := []}
def hostSignature : FuncType := {params := [.num .i64, .num .i64], results := []}

theorem module_function : wNearModule.funcs[212]? = some function := by kernel_rfl

theorem module_signature : wNearModule.types[4]? = some signature := by kernel_rfl

theorem global_signature : wNearModule.funcType? 260 = some signature := by kernel_rfl

theorem host_signature : wNearModule.funcType? 20 = some hostSignature := by kernel_rfl

theorem activation_cost (opCost : Nat) (receiver : UInt32) (len ptr : UInt64) :
    activationGas opCost #[.i32 receiver, .i64 len, .i64 ptr] = 11 * opCost := by
  simp [activationGas]

end WNear.Binary.ValueReturnLeaf
