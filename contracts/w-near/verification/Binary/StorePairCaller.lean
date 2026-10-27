import Binary.Module
import Binary.StorePair
import NearVM.Run

/-! Exact code facts for deployed f414, the immediate f566 caller on the
`ft_total_supply` path. These describe code and numeric charges, not execution. -/
namespace WNear.Binary.StorePairCaller
open Wasm Wasm.Near
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def body : Wasm.Expr :=
  [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 2, .global_set 0,
   .local_get 2, .local_get 1, .load .i64 none {align := 3, offset := 0},
   .local_get 1, .i32_const 8, .i32_binop .add,
   .load .i64 none {align := 3, offset := 0}, .call 566,
   .local_get 2, .load .i64 none {align := 3, offset := 0}, .local_set 3,
   .local_get 0, .local_get 2, .i32_const 8, .i32_binop .add,
   .load .i64 none {align := 3, offset := 0},
   .store .i64 none {align := 3, offset := 8},
   .local_get 0, .local_get 3, .store .i64 none {align := 3, offset := 0},
   .local_get 2, .i32_const 16, .i32_binop .add, .global_set 0]

def function : Func :=
  {type := 14, locals := [.num .i32, .num .i64], body, bodySize := 82}

def signature : FuncType := {params := [.num .i32, .num .i32], results := []}

/-- Forty-eight imported functions precede the defined-function vector. -/
theorem module_function : wNearModule.funcs[366]? = some function := by kernel_rfl

theorem module_signature : wNearModule.types[14]? = some signature := by kernel_rfl

theorem global_signature : wNearModule.funcType? 414 = some signature := by kernel_rfl

theorem body_length : body.length = 29 := rfl

theorem only_direct_call : body.filterMap (fun i => match i with
    | .call index => some index | _ => none) = [566] := rfl

/-- Two i32 parameters, one i32 local and one i64 local occupy twenty bytes. -/
theorem activation_cost (opCost : Nat) (out source : UInt32) :
    activationGas opCost #[.i32 out, .i32 source, .i32 0, .i64 0] = 11 * opCost := by
  simp [activationGas]

/-- The call opcode is included in f414's twenty-nine instructions. This
arithmetic excludes f414 entry activation and both administrative leaves. -/
theorem body_cost (opCost : Nat) (scratch : UInt32) (lo hi : UInt64) :
    body.length * opCost + activationGas opCost #[.i32 scratch, .i64 lo, .i64 hi] +
      WNear.Binary.StorePair.body.length * opCost = 46 * opCost := by
  simp only [body_length, WNear.Binary.StorePair.body_length, WNear.Binary.StorePair.activation_cost]
  omega

end WNear.Binary.StorePairCaller
