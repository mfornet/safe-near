import Binary.Module
import NearVM.Run

/-! Exact deployed ft_total_supply wrapper f296, defined-function entry248.
These are code and charge-shape facts, not method execution adequacy. -/
namespace WNear.Binary.TotalSupply
open Wasm Wasm.Near
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def body : Wasm.Expr :=
  [.global_get 0,
   .i32_const 144,
   .i32_binop .sub,
   .local_tee 0,
   .global_set 0,
   .call 522,
   .i32_const 1,
   .i32_const 1050188,
   .call 520,
   .local_get 0,
   .i32_const 72,
   .i32_binop .add,
   .call 219,
   .local_get 0,
   .i32_const 32,
   .i32_binop .add,
   .local_get 0,
   .i32_const 72,
   .i32_binop .add,
   .call 155,
   .local_get 0,
   .i32_const 16,
   .i32_binop .add,
   .local_get 0,
   .i32_const 32,
   .i32_binop .add,
   .call 414,
   .local_get 0,
   .local_get 0,
   .i32_const 24,
   .i32_binop .add,
   .load .i64 none {align := 3, offset := 0},
   .store .i64 none {align := 3, offset := 120},
   .local_get 0,
   .local_get 0,
   .load .i64 none {align := 3, offset := 16},
   .store .i64 none {align := 3, offset := 112},
   .local_get 0,
   .i32_const 72,
   .i32_binop .add,
   .local_get 0,
   .i32_const 112,
   .i32_binop .add,
   .call 96,
   .local_get 0,
   .i32_const 128,
   .i32_binop .add,
   .local_get 0,
   .i32_const 72,
   .i32_binop .add,
   .i32_const 1050984,
   .call 158,
   .local_get 0,
   .i32_const 8,
   .i32_binop .add,
   .local_get 0,
   .i32_const 128,
   .i32_binop .add,
   .call 779,
   .local_get 0,
   .load .i32 none {align := 2, offset := 8},
   .local_get 0,
   .load .i32 none {align := 2, offset := 12},
   .call 545,
   .local_get 0,
   .i32_const 128,
   .i32_binop .add,
   .call 68,
   .local_get 0,
   .i32_const 56,
   .i32_binop .add,
   .call 68,
   .local_get 0,
   .i32_const 144,
   .i32_binop .add,
   .global_set 0]

def function : Func := {type := 21, locals := [.num .i32], body, bodySize := 220}
def signature : FuncType := {params := [], results := []}

theorem module_function : wNearModule.funcs[248]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[21]? = some signature := by kernel_rfl
theorem global_signature : wNearModule.funcType? 296 = some signature := by kernel_rfl

theorem exported : ((wNearModule.exports.toList.find? (fun e => e.name == "ft_total_supply")).map (·.desc)) =
    some (.func 296) := by kernel_rfl

theorem body_length : body.length = 76 := rfl

def callees : List Nat := [522, 520, 219, 155, 414, 96, 158, 779, 545, 68, 68]

theorem direct_calls : body.filterMap (fun i => match i with | .call index => some index | _ => none) = callees := rfl

theorem call_count : callees.length = 11 := rfl

theorem scalar_count : (body.filter (fun i => match i with | .call _ => false | _ => true)).length = 65 := rfl

/-- One i32 local is the only value in the wrapper's zero-parameter frame. -/
theorem activation_cost (opCost : Nat) : activationGas opCost #[.i32 0] = 9 * opCost := by
  simp [activationGas]

end WNear.Binary.TotalSupply
