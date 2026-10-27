import Binary.Module
import NearVM.Run

/-! Exact code facts for deployed f779 on the total-supply path. -/
namespace WNear.Binary.PackWords
open Wasm Wasm.Near
set_option maxRecDepth 10000

/-- The second load follows the first store, so overlapping ranges retain
their sequential Wasm meaning. -/
def body : Expr :=
  [.local_get 0, .local_get 1, .load .i32 none {align := 2, offset := 8},
   .store .i32 none {align := 2, offset := 4},
   .local_get 0, .local_get 1, .load .i32 none {align := 2, offset := 0},
   .store .i32 none {align := 2, offset := 0}]

def function : Func := {type := 14, locals := [], body, bodySize := 22}

def signature : FuncType := {params := [.num .i32, .num .i32], results := []}

theorem module_function : wNearModule.funcs[731]? = some function := by kernel_rfl

theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl

theorem global_signature : wNearModule.funcType? 779 = some signature := by kernel_rfl

theorem body_length : body.length = 8 := rfl

theorem activation_cost (opCost : Nat) (out source : UInt32) :
    activationGas opCost #[.i32 out, .i32 source] = 9 * opCost := by
  simp [activationGas]

end WNear.Binary.PackWords
