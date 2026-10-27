import Binary.Module
import NearVM.Run

/-! Actual eight-byte initializer called indirectly by the lazy interface path. -/
namespace WNear.Binary.InterfaceInitialize
open Wasm Wasm.Near
set_option maxRecDepth 20000

def body : Expr := [.local_get 0, .i64_const 0, .store .i64 none {align := 2, offset := 0}]
def function : Func := {type := 0, locals := [], body, bodySize := 9}
def signature : FuncType := {params := [.num .i32], results := []}

theorem module_function : wNearModule.funcs[516]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[0]? = some signature := by kernel_rfl
theorem table_element : (wNearModule.elems[0]!).init[105]? = some [.ref_func 564] := by kernel_rfl

theorem activation_cost (op : Nat) (pointer : UInt32) : activationGas op #[.i32 pointer] = 9 * op := by
  simp [activationGas]

end WNear.Binary.InterfaceInitialize
