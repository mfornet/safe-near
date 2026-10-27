import Binary.Module
import NearVM.Run

/-! Kernel facts for the actual deployed f158 (`Result::expect`). -/
namespace WNear.Binary.ExpectResult
open Wasm Wasm.Near
set_option maxRecDepth 20000

/-- Reserve sixteen bytes by wrapping UInt32 arithmetic; the accepted branch
never accesses this scratch memory. -/
def prologue : Expr :=
  [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 3, .global_set 0]

def tagCheck : Expr :=
  [.local_get 1, .load .i32 none {align := 2, offset := 0}, .i32_const 1,
   .i32_relop .ne, .br_if 0]

/-- Only discriminant one falls through to this actual panic call. -/
def panicTail : Expr :=
  [.local_get 3, .local_get 1, .load .i32 none {align := 2, offset := 4},
   .store .i32 none {align := 2, offset := 12},
   .i32_const 1050404, .i32_const 48, .local_get 3, .i32_const 12, .i32_binop .add,
   .i32_const 1049036, .local_get 2, .call 881, .unreachable]

def copyLow : Expr :=
  [.local_get 0, .local_get 1, .load .i64 none {align := 2, offset := 4},
   .store .i64 none {align := 2, offset := 0}]

def copyHigh : Expr :=
  [.local_get 0, .i32_const 8, .i32_binop .add, .local_get 1, .i32_const 12,
   .i32_binop .add, .load .i32 none {align := 2, offset := 0},
   .store .i32 none {align := 2, offset := 0}]

def epilogue : Expr := [.local_get 3, .i32_const 16, .i32_binop .add, .global_set 0]

def body : Expr :=
  prologue ++ [.block .empty (tagCheck ++ panicTail)] ++ copyLow ++ copyHigh ++ epilogue

def function : Func := {type := 31, locals := [.num .i32], body, bodySize := 109}

def signature : FuncType :=
  {params := [.num .i32, .num .i32, .num .i32], results := []}

theorem module_function : wNearModule.funcs[110]? = some function := by kernel_rfl

theorem module_signature : wNearModule.types[31]? = some signature := by kernel_rfl

theorem global_signature : wNearModule.funcType? 158 = some signature := by kernel_rfl

theorem body_length : body.length = 22 := rfl

/-- The block is free; its five executed guard instructions add to the 21
non-block top-level instructions. Panic-tail instructions are not counted. -/
theorem accepted_paid_length :
    prologue.length + tagCheck.length + copyLow.length + copyHigh.length + epilogue.length = 26 := rfl

theorem activation_cost (opCost : Nat) (out source location : UInt32) :
    activationGas opCost #[.i32 out, .i32 source, .i32 location, .i32 0] = 10 * opCost := by
  simp [activationGas]

end WNear.Binary.ExpectResult
