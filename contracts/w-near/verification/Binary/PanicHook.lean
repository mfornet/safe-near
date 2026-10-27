import Binary.Module
import NearVM.Run

/-! Exact deployed panic-hook setup entry f522. -/
namespace WNear.Binary.PanicHook
open Wasm Wasm.Near
set_option maxRecDepth 20000

def body : Expr := [.i32_const 0, .i32_const 1, .call 503, .i32_const 1055136, .call 822]
def function : Func := {type := 21, locals := [], body, bodySize := 24}
def signature : FuncType := {params := [], results := []}

theorem module_function : wNearModule.funcs[474]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[21]? = some signature := by kernel_rfl
theorem activation_cost (op : Nat) : activationGas op (#[] : Array Value) = 8 * op := by simp [activationGas]
end WNear.Binary.PanicHook
