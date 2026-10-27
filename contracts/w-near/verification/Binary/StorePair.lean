import Binary.Module
import NearVM.Run

/-! Kernel code facts for the actual deployed two-word store helper f566,
called by f414 on the `ft_total_supply` path. No body is substituted for the
binary: `module_function` identifies this literal in its decoded function table. -/
namespace WNear.Binary.StorePair
open Wasm Wasm.Near
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def body : Wasm.Expr :=
  [.local_get 0, .local_get 2, .store .i64 none {align := 3, offset := 8},
   .local_get 0, .local_get 1, .store .i64 none {align := 3, offset := 0}]

def function : Func := {type := 4, locals := [], body, bodySize := 16}
def signature : FuncType := {params := [.num .i32, .num .i64, .num .i64], results := []}

/-- Index 518 in the defined-function vector is global function 566. -/
theorem module_function : wNearModule.funcs[518]? = some function := by kernel_rfl

theorem module_signature : wNearModule.types[4]? = some signature := by kernel_rfl

theorem global_signature : wNearModule.funcType? 566 = some signature := by kernel_rfl

theorem body_length : body.length = 6 := rfl

/-- Function entry charges 64 fixed bytes and 20 bytes of typed arguments,
rounded up to eleven units. The caller opcode is separate. -/
theorem activation_cost (opCost : Nat) (out : UInt32) (low high : UInt64) :
    activationGas opCost #[.i32 out, .i64 low, .i64 high] = 11 * opCost := by
  simp [activationGas]

end WNear.Binary.StorePair
