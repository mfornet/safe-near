import Binary.ValueReturnLeaf

/-! Actual trait-dispatch fragment inside deployed f456, called by f545. -/
namespace WNear.Binary.ValueReturnDispatch
open Wasm
set_option maxRecDepth 20000

def dispatch : Expr :=
  [.local_tee 3, .load .i32 none {align := 2, offset := 0},
   .local_get 1, .load .i64 (some {bits := 32, signed := false}) {align := 2, offset := 4},
   .local_get 1, .load .i64 (some {bits := 32, signed := false}) {align := 2, offset := 0},
   .local_get 3, .load .i32 none {align := 2, offset := 4},
   .load .i32 none {align := 2, offset := 92}, .call_indirect 4 0]

/-- Select the nested successful borrowing branch from the actual decoded body. -/
noncomputable def innerBody : Expr :=
  match f456.body[5]? with
  | some (Instr.block _ (Instr.block _ body :: _)) => body
  | _ => []

theorem fragment : (innerBody.drop 28).take 10 = dispatch := by rfl

theorem dispatch_length : dispatch.length = 10 := rfl

theorem module_function : wNearModule.funcs[408]? = some f456 := by kernel_rfl

theorem wrapper_function : wNearModule.funcs[497]? = some f545 := by kernel_rfl

end WNear.Binary.ValueReturnDispatch
